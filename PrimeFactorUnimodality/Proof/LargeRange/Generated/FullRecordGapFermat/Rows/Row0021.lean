import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue05121 : Nat := fullRecordGapCenterValue + 237086

theorem fullRecordGapTerm05121_eq_value :
    recordGapCenter + 237086 = fullRecordGapValue05121 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05121_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05121 (fullRecordGapValue05121 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05121_not_prime : ¬(recordGapCenter + 237086).Prime := by
  rw [fullRecordGapTerm05121_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05121, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05121_fast_pow_mod_ne_one

def fullRecordGapValue05122 : Nat := fullRecordGapCenterValue + 237092

theorem fullRecordGapTerm05122_eq_value :
    recordGapCenter + 237092 = fullRecordGapValue05122 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05122_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05122 (fullRecordGapValue05122 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05122_not_prime : ¬(recordGapCenter + 237092).Prime := by
  rw [fullRecordGapTerm05122_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05122, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05122_fast_pow_mod_ne_one

def fullRecordGapValue05123 : Nat := fullRecordGapCenterValue + 237098

theorem fullRecordGapTerm05123_eq_value :
    recordGapCenter + 237098 = fullRecordGapValue05123 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05123_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05123 (fullRecordGapValue05123 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05123_not_prime : ¬(recordGapCenter + 237098).Prime := by
  rw [fullRecordGapTerm05123_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05123, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05123_fast_pow_mod_ne_one

def fullRecordGapValue05124 : Nat := fullRecordGapCenterValue + 237206

theorem fullRecordGapTerm05124_eq_value :
    recordGapCenter + 237206 = fullRecordGapValue05124 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05124_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05124 (fullRecordGapValue05124 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05124_not_prime : ¬(recordGapCenter + 237206).Prime := by
  rw [fullRecordGapTerm05124_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05124, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05124_fast_pow_mod_ne_one

def fullRecordGapValue05125 : Nat := fullRecordGapCenterValue + 237338

theorem fullRecordGapTerm05125_eq_value :
    recordGapCenter + 237338 = fullRecordGapValue05125 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05125_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05125 (fullRecordGapValue05125 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05125_not_prime : ¬(recordGapCenter + 237338).Prime := by
  rw [fullRecordGapTerm05125_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05125, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05125_fast_pow_mod_ne_one

def fullRecordGapValue05126 : Nat := fullRecordGapCenterValue + 237476

theorem fullRecordGapTerm05126_eq_value :
    recordGapCenter + 237476 = fullRecordGapValue05126 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05126_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05126 (fullRecordGapValue05126 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05126_not_prime : ¬(recordGapCenter + 237476).Prime := by
  rw [fullRecordGapTerm05126_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05126, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05126_fast_pow_mod_ne_one

def fullRecordGapValue05127 : Nat := fullRecordGapCenterValue + 237788

theorem fullRecordGapTerm05127_eq_value :
    recordGapCenter + 237788 = fullRecordGapValue05127 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05127_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05127 (fullRecordGapValue05127 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05127_not_prime : ¬(recordGapCenter + 237788).Prime := by
  rw [fullRecordGapTerm05127_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05127, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05127_fast_pow_mod_ne_one

def fullRecordGapValue05128 : Nat := fullRecordGapCenterValue + 237806

theorem fullRecordGapTerm05128_eq_value :
    recordGapCenter + 237806 = fullRecordGapValue05128 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05128_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05128 (fullRecordGapValue05128 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05128_not_prime : ¬(recordGapCenter + 237806).Prime := by
  rw [fullRecordGapTerm05128_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05128, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05128_fast_pow_mod_ne_one

def fullRecordGapValue05129 : Nat := fullRecordGapCenterValue + 237812

theorem fullRecordGapTerm05129_eq_value :
    recordGapCenter + 237812 = fullRecordGapValue05129 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05129_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05129 (fullRecordGapValue05129 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05129_not_prime : ¬(recordGapCenter + 237812).Prime := by
  rw [fullRecordGapTerm05129_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05129, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05129_fast_pow_mod_ne_one

def fullRecordGapValue05130 : Nat := fullRecordGapCenterValue + 238052

theorem fullRecordGapTerm05130_eq_value :
    recordGapCenter + 238052 = fullRecordGapValue05130 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05130_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05130 (fullRecordGapValue05130 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05130_not_prime : ¬(recordGapCenter + 238052).Prime := by
  rw [fullRecordGapTerm05130_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05130, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05130_fast_pow_mod_ne_one

def fullRecordGapValue05131 : Nat := fullRecordGapCenterValue + 238140

theorem fullRecordGapTerm05131_eq_value :
    recordGapCenter + 238140 = fullRecordGapValue05131 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05131_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05131 (fullRecordGapValue05131 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05131_not_prime : ¬(recordGapCenter + 238140).Prime := by
  rw [fullRecordGapTerm05131_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05131, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05131_fast_pow_mod_ne_one

def fullRecordGapValue05132 : Nat := fullRecordGapCenterValue + 238262

theorem fullRecordGapTerm05132_eq_value :
    recordGapCenter + 238262 = fullRecordGapValue05132 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05132_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05132 (fullRecordGapValue05132 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05132_not_prime : ¬(recordGapCenter + 238262).Prime := by
  rw [fullRecordGapTerm05132_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05132, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05132_fast_pow_mod_ne_one

def fullRecordGapValue05133 : Nat := fullRecordGapCenterValue + 238268

theorem fullRecordGapTerm05133_eq_value :
    recordGapCenter + 238268 = fullRecordGapValue05133 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05133_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05133 (fullRecordGapValue05133 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05133_not_prime : ¬(recordGapCenter + 238268).Prime := by
  rw [fullRecordGapTerm05133_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05133, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05133_fast_pow_mod_ne_one

def fullRecordGapValue05134 : Nat := fullRecordGapCenterValue + 238346

theorem fullRecordGapTerm05134_eq_value :
    recordGapCenter + 238346 = fullRecordGapValue05134 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05134_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05134 (fullRecordGapValue05134 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05134_not_prime : ¬(recordGapCenter + 238346).Prime := by
  rw [fullRecordGapTerm05134_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05134, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05134_fast_pow_mod_ne_one

def fullRecordGapValue05135 : Nat := fullRecordGapCenterValue + 238358

theorem fullRecordGapTerm05135_eq_value :
    recordGapCenter + 238358 = fullRecordGapValue05135 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05135_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05135 (fullRecordGapValue05135 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05135_not_prime : ¬(recordGapCenter + 238358).Prime := by
  rw [fullRecordGapTerm05135_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05135, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05135_fast_pow_mod_ne_one

def fullRecordGapValue05136 : Nat := fullRecordGapCenterValue + 238466

theorem fullRecordGapTerm05136_eq_value :
    recordGapCenter + 238466 = fullRecordGapValue05136 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05136_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05136 (fullRecordGapValue05136 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05136_not_prime : ¬(recordGapCenter + 238466).Prime := by
  rw [fullRecordGapTerm05136_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05136, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05136_fast_pow_mod_ne_one

def fullRecordGapValue05137 : Nat := fullRecordGapCenterValue + 238598

theorem fullRecordGapTerm05137_eq_value :
    recordGapCenter + 238598 = fullRecordGapValue05137 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05137_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05137 (fullRecordGapValue05137 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05137_not_prime : ¬(recordGapCenter + 238598).Prime := by
  rw [fullRecordGapTerm05137_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05137, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05137_fast_pow_mod_ne_one

def fullRecordGapValue05138 : Nat := fullRecordGapCenterValue + 238778

theorem fullRecordGapTerm05138_eq_value :
    recordGapCenter + 238778 = fullRecordGapValue05138 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05138_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05138 (fullRecordGapValue05138 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05138_not_prime : ¬(recordGapCenter + 238778).Prime := by
  rw [fullRecordGapTerm05138_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05138, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05138_fast_pow_mod_ne_one

def fullRecordGapValue05139 : Nat := fullRecordGapCenterValue + 238796

theorem fullRecordGapTerm05139_eq_value :
    recordGapCenter + 238796 = fullRecordGapValue05139 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05139_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05139 (fullRecordGapValue05139 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05139_not_prime : ¬(recordGapCenter + 238796).Prime := by
  rw [fullRecordGapTerm05139_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05139, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05139_fast_pow_mod_ne_one

def fullRecordGapValue05140 : Nat := fullRecordGapCenterValue + 238892

theorem fullRecordGapTerm05140_eq_value :
    recordGapCenter + 238892 = fullRecordGapValue05140 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05140_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05140 (fullRecordGapValue05140 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05140_not_prime : ¬(recordGapCenter + 238892).Prime := by
  rw [fullRecordGapTerm05140_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05140, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05140_fast_pow_mod_ne_one

def fullRecordGapValue05141 : Nat := fullRecordGapCenterValue + 238988

theorem fullRecordGapTerm05141_eq_value :
    recordGapCenter + 238988 = fullRecordGapValue05141 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05141_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05141 (fullRecordGapValue05141 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05141_not_prime : ¬(recordGapCenter + 238988).Prime := by
  rw [fullRecordGapTerm05141_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05141, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05141_fast_pow_mod_ne_one

def fullRecordGapValue05142 : Nat := fullRecordGapCenterValue + 239066

theorem fullRecordGapTerm05142_eq_value :
    recordGapCenter + 239066 = fullRecordGapValue05142 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05142_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05142 (fullRecordGapValue05142 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05142_not_prime : ¬(recordGapCenter + 239066).Prime := by
  rw [fullRecordGapTerm05142_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05142, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05142_fast_pow_mod_ne_one

def fullRecordGapValue05143 : Nat := fullRecordGapCenterValue + 239138

theorem fullRecordGapTerm05143_eq_value :
    recordGapCenter + 239138 = fullRecordGapValue05143 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05143_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05143 (fullRecordGapValue05143 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05143_not_prime : ¬(recordGapCenter + 239138).Prime := by
  rw [fullRecordGapTerm05143_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05143, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05143_fast_pow_mod_ne_one

def fullRecordGapValue05144 : Nat := fullRecordGapCenterValue + 239222

theorem fullRecordGapTerm05144_eq_value :
    recordGapCenter + 239222 = fullRecordGapValue05144 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05144_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05144 (fullRecordGapValue05144 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05144_not_prime : ¬(recordGapCenter + 239222).Prime := by
  rw [fullRecordGapTerm05144_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05144, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05144_fast_pow_mod_ne_one

def fullRecordGapValue05145 : Nat := fullRecordGapCenterValue + 239516

theorem fullRecordGapTerm05145_eq_value :
    recordGapCenter + 239516 = fullRecordGapValue05145 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05145_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05145 (fullRecordGapValue05145 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05145_not_prime : ¬(recordGapCenter + 239516).Prime := by
  rw [fullRecordGapTerm05145_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05145, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05145_fast_pow_mod_ne_one

def fullRecordGapValue05146 : Nat := fullRecordGapCenterValue + 239762

theorem fullRecordGapTerm05146_eq_value :
    recordGapCenter + 239762 = fullRecordGapValue05146 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05146_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05146 (fullRecordGapValue05146 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05146_not_prime : ¬(recordGapCenter + 239762).Prime := by
  rw [fullRecordGapTerm05146_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05146, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05146_fast_pow_mod_ne_one

def fullRecordGapValue05147 : Nat := fullRecordGapCenterValue + 239828

theorem fullRecordGapTerm05147_eq_value :
    recordGapCenter + 239828 = fullRecordGapValue05147 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05147_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05147 (fullRecordGapValue05147 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05147_not_prime : ¬(recordGapCenter + 239828).Prime := by
  rw [fullRecordGapTerm05147_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05147, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05147_fast_pow_mod_ne_one

def fullRecordGapValue05148 : Nat := fullRecordGapCenterValue + 239846

theorem fullRecordGapTerm05148_eq_value :
    recordGapCenter + 239846 = fullRecordGapValue05148 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05148_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05148 (fullRecordGapValue05148 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05148_not_prime : ¬(recordGapCenter + 239846).Prime := by
  rw [fullRecordGapTerm05148_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05148, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05148_fast_pow_mod_ne_one

def fullRecordGapValue05149 : Nat := fullRecordGapCenterValue + 239858

theorem fullRecordGapTerm05149_eq_value :
    recordGapCenter + 239858 = fullRecordGapValue05149 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05149_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05149 (fullRecordGapValue05149 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05149_not_prime : ¬(recordGapCenter + 239858).Prime := by
  rw [fullRecordGapTerm05149_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05149, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05149_fast_pow_mod_ne_one

def fullRecordGapValue05150 : Nat := fullRecordGapCenterValue + 239996

theorem fullRecordGapTerm05150_eq_value :
    recordGapCenter + 239996 = fullRecordGapValue05150 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05150_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05150 (fullRecordGapValue05150 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05150_not_prime : ¬(recordGapCenter + 239996).Prime := by
  rw [fullRecordGapTerm05150_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05150, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05150_fast_pow_mod_ne_one

def fullRecordGapValue05151 : Nat := fullRecordGapCenterValue + 240000

theorem fullRecordGapTerm05151_eq_value :
    recordGapCenter + 240000 = fullRecordGapValue05151 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05151_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05151 (fullRecordGapValue05151 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05151_not_prime : ¬(recordGapCenter + 240000).Prime := by
  rw [fullRecordGapTerm05151_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05151, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05151_fast_pow_mod_ne_one

def fullRecordGapValue05152 : Nat := fullRecordGapCenterValue + 240068

theorem fullRecordGapTerm05152_eq_value :
    recordGapCenter + 240068 = fullRecordGapValue05152 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05152_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05152 (fullRecordGapValue05152 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05152_not_prime : ¬(recordGapCenter + 240068).Prime := by
  rw [fullRecordGapTerm05152_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05152, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05152_fast_pow_mod_ne_one

def fullRecordGapValue05153 : Nat := fullRecordGapCenterValue + 240098

theorem fullRecordGapTerm05153_eq_value :
    recordGapCenter + 240098 = fullRecordGapValue05153 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05153_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05153 (fullRecordGapValue05153 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05153_not_prime : ¬(recordGapCenter + 240098).Prime := by
  rw [fullRecordGapTerm05153_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05153, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05153_fast_pow_mod_ne_one

def fullRecordGapValue05154 : Nat := fullRecordGapCenterValue + 240158

theorem fullRecordGapTerm05154_eq_value :
    recordGapCenter + 240158 = fullRecordGapValue05154 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05154_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05154 (fullRecordGapValue05154 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05154_not_prime : ¬(recordGapCenter + 240158).Prime := by
  rw [fullRecordGapTerm05154_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05154, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05154_fast_pow_mod_ne_one

def fullRecordGapValue05155 : Nat := fullRecordGapCenterValue + 240182

theorem fullRecordGapTerm05155_eq_value :
    recordGapCenter + 240182 = fullRecordGapValue05155 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05155_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05155 (fullRecordGapValue05155 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05155_not_prime : ¬(recordGapCenter + 240182).Prime := by
  rw [fullRecordGapTerm05155_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05155, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05155_fast_pow_mod_ne_one

def fullRecordGapValue05156 : Nat := fullRecordGapCenterValue + 240206

theorem fullRecordGapTerm05156_eq_value :
    recordGapCenter + 240206 = fullRecordGapValue05156 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05156_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05156 (fullRecordGapValue05156 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05156_not_prime : ¬(recordGapCenter + 240206).Prime := by
  rw [fullRecordGapTerm05156_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05156, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05156_fast_pow_mod_ne_one

def fullRecordGapValue05157 : Nat := fullRecordGapCenterValue + 240242

theorem fullRecordGapTerm05157_eq_value :
    recordGapCenter + 240242 = fullRecordGapValue05157 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05157_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05157 (fullRecordGapValue05157 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05157_not_prime : ¬(recordGapCenter + 240242).Prime := by
  rw [fullRecordGapTerm05157_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05157, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05157_fast_pow_mod_ne_one

def fullRecordGapValue05158 : Nat := fullRecordGapCenterValue + 240308

theorem fullRecordGapTerm05158_eq_value :
    recordGapCenter + 240308 = fullRecordGapValue05158 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05158_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05158 (fullRecordGapValue05158 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05158_not_prime : ¬(recordGapCenter + 240308).Prime := by
  rw [fullRecordGapTerm05158_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05158, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05158_fast_pow_mod_ne_one

def fullRecordGapValue05159 : Nat := fullRecordGapCenterValue + 240356

theorem fullRecordGapTerm05159_eq_value :
    recordGapCenter + 240356 = fullRecordGapValue05159 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05159_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05159 (fullRecordGapValue05159 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05159_not_prime : ¬(recordGapCenter + 240356).Prime := by
  rw [fullRecordGapTerm05159_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05159, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05159_fast_pow_mod_ne_one

def fullRecordGapValue05160 : Nat := fullRecordGapCenterValue + 240446

theorem fullRecordGapTerm05160_eq_value :
    recordGapCenter + 240446 = fullRecordGapValue05160 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05160_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05160 (fullRecordGapValue05160 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05160_not_prime : ¬(recordGapCenter + 240446).Prime := by
  rw [fullRecordGapTerm05160_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05160, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05160_fast_pow_mod_ne_one

def fullRecordGapValue05161 : Nat := fullRecordGapCenterValue + 240570

theorem fullRecordGapTerm05161_eq_value :
    recordGapCenter + 240570 = fullRecordGapValue05161 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05161_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05161 (fullRecordGapValue05161 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05161_not_prime : ¬(recordGapCenter + 240570).Prime := by
  rw [fullRecordGapTerm05161_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05161, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05161_fast_pow_mod_ne_one

def fullRecordGapValue05162 : Nat := fullRecordGapCenterValue + 240662

theorem fullRecordGapTerm05162_eq_value :
    recordGapCenter + 240662 = fullRecordGapValue05162 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05162_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05162 (fullRecordGapValue05162 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05162_not_prime : ¬(recordGapCenter + 240662).Prime := by
  rw [fullRecordGapTerm05162_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05162, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05162_fast_pow_mod_ne_one

def fullRecordGapValue05163 : Nat := fullRecordGapCenterValue + 240836

theorem fullRecordGapTerm05163_eq_value :
    recordGapCenter + 240836 = fullRecordGapValue05163 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05163_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05163 (fullRecordGapValue05163 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05163_not_prime : ¬(recordGapCenter + 240836).Prime := by
  rw [fullRecordGapTerm05163_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05163, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05163_fast_pow_mod_ne_one

def fullRecordGapValue05164 : Nat := fullRecordGapCenterValue + 241238

theorem fullRecordGapTerm05164_eq_value :
    recordGapCenter + 241238 = fullRecordGapValue05164 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05164_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05164 (fullRecordGapValue05164 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05164_not_prime : ¬(recordGapCenter + 241238).Prime := by
  rw [fullRecordGapTerm05164_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05164, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05164_fast_pow_mod_ne_one

def fullRecordGapValue05165 : Nat := fullRecordGapCenterValue + 241382

theorem fullRecordGapTerm05165_eq_value :
    recordGapCenter + 241382 = fullRecordGapValue05165 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05165_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05165 (fullRecordGapValue05165 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05165_not_prime : ¬(recordGapCenter + 241382).Prime := by
  rw [fullRecordGapTerm05165_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05165, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05165_fast_pow_mod_ne_one

def fullRecordGapValue05166 : Nat := fullRecordGapCenterValue + 241442

theorem fullRecordGapTerm05166_eq_value :
    recordGapCenter + 241442 = fullRecordGapValue05166 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05166_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05166 (fullRecordGapValue05166 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05166_not_prime : ¬(recordGapCenter + 241442).Prime := by
  rw [fullRecordGapTerm05166_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05166, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05166_fast_pow_mod_ne_one

def fullRecordGapValue05167 : Nat := fullRecordGapCenterValue + 241472

theorem fullRecordGapTerm05167_eq_value :
    recordGapCenter + 241472 = fullRecordGapValue05167 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05167_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05167 (fullRecordGapValue05167 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05167_not_prime : ¬(recordGapCenter + 241472).Prime := by
  rw [fullRecordGapTerm05167_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05167, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05167_fast_pow_mod_ne_one

def fullRecordGapValue05168 : Nat := fullRecordGapCenterValue + 241652

theorem fullRecordGapTerm05168_eq_value :
    recordGapCenter + 241652 = fullRecordGapValue05168 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05168_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05168 (fullRecordGapValue05168 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05168_not_prime : ¬(recordGapCenter + 241652).Prime := by
  rw [fullRecordGapTerm05168_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05168, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05168_fast_pow_mod_ne_one

def fullRecordGapValue05169 : Nat := fullRecordGapCenterValue + 241742

theorem fullRecordGapTerm05169_eq_value :
    recordGapCenter + 241742 = fullRecordGapValue05169 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05169_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05169 (fullRecordGapValue05169 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05169_not_prime : ¬(recordGapCenter + 241742).Prime := by
  rw [fullRecordGapTerm05169_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05169, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05169_fast_pow_mod_ne_one

def fullRecordGapValue05170 : Nat := fullRecordGapCenterValue + 241778

theorem fullRecordGapTerm05170_eq_value :
    recordGapCenter + 241778 = fullRecordGapValue05170 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05170_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05170 (fullRecordGapValue05170 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05170_not_prime : ¬(recordGapCenter + 241778).Prime := by
  rw [fullRecordGapTerm05170_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05170, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05170_fast_pow_mod_ne_one

def fullRecordGapValue05171 : Nat := fullRecordGapCenterValue + 241796

theorem fullRecordGapTerm05171_eq_value :
    recordGapCenter + 241796 = fullRecordGapValue05171 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05171_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05171 (fullRecordGapValue05171 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05171_not_prime : ¬(recordGapCenter + 241796).Prime := by
  rw [fullRecordGapTerm05171_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05171, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05171_fast_pow_mod_ne_one

def fullRecordGapValue05172 : Nat := fullRecordGapCenterValue + 241920

theorem fullRecordGapTerm05172_eq_value :
    recordGapCenter + 241920 = fullRecordGapValue05172 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05172_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05172 (fullRecordGapValue05172 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05172_not_prime : ¬(recordGapCenter + 241920).Prime := by
  rw [fullRecordGapTerm05172_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05172, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05172_fast_pow_mod_ne_one

def fullRecordGapValue05173 : Nat := fullRecordGapCenterValue + 242036

theorem fullRecordGapTerm05173_eq_value :
    recordGapCenter + 242036 = fullRecordGapValue05173 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05173_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05173 (fullRecordGapValue05173 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05173_not_prime : ¬(recordGapCenter + 242036).Prime := by
  rw [fullRecordGapTerm05173_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05173, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05173_fast_pow_mod_ne_one

def fullRecordGapValue05174 : Nat := fullRecordGapCenterValue + 242126

theorem fullRecordGapTerm05174_eq_value :
    recordGapCenter + 242126 = fullRecordGapValue05174 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05174_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05174 (fullRecordGapValue05174 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05174_not_prime : ¬(recordGapCenter + 242126).Prime := by
  rw [fullRecordGapTerm05174_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05174, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05174_fast_pow_mod_ne_one

def fullRecordGapValue05175 : Nat := fullRecordGapCenterValue + 242246

theorem fullRecordGapTerm05175_eq_value :
    recordGapCenter + 242246 = fullRecordGapValue05175 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05175_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05175 (fullRecordGapValue05175 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05175_not_prime : ¬(recordGapCenter + 242246).Prime := by
  rw [fullRecordGapTerm05175_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05175, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05175_fast_pow_mod_ne_one

def fullRecordGapValue05176 : Nat := fullRecordGapCenterValue + 242342

theorem fullRecordGapTerm05176_eq_value :
    recordGapCenter + 242342 = fullRecordGapValue05176 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05176_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05176 (fullRecordGapValue05176 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05176_not_prime : ¬(recordGapCenter + 242342).Prime := by
  rw [fullRecordGapTerm05176_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05176, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05176_fast_pow_mod_ne_one

def fullRecordGapValue05177 : Nat := fullRecordGapCenterValue + 242492

theorem fullRecordGapTerm05177_eq_value :
    recordGapCenter + 242492 = fullRecordGapValue05177 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05177_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05177 (fullRecordGapValue05177 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05177_not_prime : ¬(recordGapCenter + 242492).Prime := by
  rw [fullRecordGapTerm05177_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05177, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05177_fast_pow_mod_ne_one

def fullRecordGapValue05178 : Nat := fullRecordGapCenterValue + 242550

theorem fullRecordGapTerm05178_eq_value :
    recordGapCenter + 242550 = fullRecordGapValue05178 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05178_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05178 (fullRecordGapValue05178 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05178_not_prime : ¬(recordGapCenter + 242550).Prime := by
  rw [fullRecordGapTerm05178_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05178, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05178_fast_pow_mod_ne_one

def fullRecordGapValue05179 : Nat := fullRecordGapCenterValue + 242582

theorem fullRecordGapTerm05179_eq_value :
    recordGapCenter + 242582 = fullRecordGapValue05179 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05179_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05179 (fullRecordGapValue05179 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05179_not_prime : ¬(recordGapCenter + 242582).Prime := by
  rw [fullRecordGapTerm05179_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05179, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05179_fast_pow_mod_ne_one

def fullRecordGapValue05180 : Nat := fullRecordGapCenterValue + 243062

theorem fullRecordGapTerm05180_eq_value :
    recordGapCenter + 243062 = fullRecordGapValue05180 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05180_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05180 (fullRecordGapValue05180 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05180_not_prime : ¬(recordGapCenter + 243062).Prime := by
  rw [fullRecordGapTerm05180_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05180, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05180_fast_pow_mod_ne_one

def fullRecordGapValue05181 : Nat := fullRecordGapCenterValue + 243266

theorem fullRecordGapTerm05181_eq_value :
    recordGapCenter + 243266 = fullRecordGapValue05181 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05181_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05181 (fullRecordGapValue05181 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05181_not_prime : ¬(recordGapCenter + 243266).Prime := by
  rw [fullRecordGapTerm05181_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05181, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05181_fast_pow_mod_ne_one

def fullRecordGapValue05182 : Nat := fullRecordGapCenterValue + 243476

theorem fullRecordGapTerm05182_eq_value :
    recordGapCenter + 243476 = fullRecordGapValue05182 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05182_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05182 (fullRecordGapValue05182 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05182_not_prime : ¬(recordGapCenter + 243476).Prime := by
  rw [fullRecordGapTerm05182_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05182, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05182_fast_pow_mod_ne_one

def fullRecordGapValue05183 : Nat := fullRecordGapCenterValue + 243548

theorem fullRecordGapTerm05183_eq_value :
    recordGapCenter + 243548 = fullRecordGapValue05183 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05183_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05183 (fullRecordGapValue05183 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05183_not_prime : ¬(recordGapCenter + 243548).Prime := by
  rw [fullRecordGapTerm05183_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05183, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05183_fast_pow_mod_ne_one

def fullRecordGapValue05184 : Nat := fullRecordGapCenterValue + 243692

theorem fullRecordGapTerm05184_eq_value :
    recordGapCenter + 243692 = fullRecordGapValue05184 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05184_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05184 (fullRecordGapValue05184 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05184_not_prime : ¬(recordGapCenter + 243692).Prime := by
  rw [fullRecordGapTerm05184_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05184, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05184_fast_pow_mod_ne_one

def fullRecordGapValue05185 : Nat := fullRecordGapCenterValue + 243842

theorem fullRecordGapTerm05185_eq_value :
    recordGapCenter + 243842 = fullRecordGapValue05185 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05185_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05185 (fullRecordGapValue05185 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05185_not_prime : ¬(recordGapCenter + 243842).Prime := by
  rw [fullRecordGapTerm05185_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05185, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05185_fast_pow_mod_ne_one

def fullRecordGapValue05186 : Nat := fullRecordGapCenterValue + 243926

theorem fullRecordGapTerm05186_eq_value :
    recordGapCenter + 243926 = fullRecordGapValue05186 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05186_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05186 (fullRecordGapValue05186 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05186_not_prime : ¬(recordGapCenter + 243926).Prime := by
  rw [fullRecordGapTerm05186_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05186, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05186_fast_pow_mod_ne_one

def fullRecordGapValue05187 : Nat := fullRecordGapCenterValue + 243936

theorem fullRecordGapTerm05187_eq_value :
    recordGapCenter + 243936 = fullRecordGapValue05187 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05187_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05187 (fullRecordGapValue05187 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05187_not_prime : ¬(recordGapCenter + 243936).Prime := by
  rw [fullRecordGapTerm05187_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05187, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05187_fast_pow_mod_ne_one

def fullRecordGapValue05188 : Nat := fullRecordGapCenterValue + 243986

theorem fullRecordGapTerm05188_eq_value :
    recordGapCenter + 243986 = fullRecordGapValue05188 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05188_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05188 (fullRecordGapValue05188 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05188_not_prime : ¬(recordGapCenter + 243986).Prime := by
  rw [fullRecordGapTerm05188_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05188, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05188_fast_pow_mod_ne_one

def fullRecordGapValue05189 : Nat := fullRecordGapCenterValue + 244058

theorem fullRecordGapTerm05189_eq_value :
    recordGapCenter + 244058 = fullRecordGapValue05189 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05189_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05189 (fullRecordGapValue05189 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05189_not_prime : ¬(recordGapCenter + 244058).Prime := by
  rw [fullRecordGapTerm05189_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05189, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05189_fast_pow_mod_ne_one

def fullRecordGapValue05190 : Nat := fullRecordGapCenterValue + 244406

theorem fullRecordGapTerm05190_eq_value :
    recordGapCenter + 244406 = fullRecordGapValue05190 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05190_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05190 (fullRecordGapValue05190 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05190_not_prime : ¬(recordGapCenter + 244406).Prime := by
  rw [fullRecordGapTerm05190_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05190, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05190_fast_pow_mod_ne_one

def fullRecordGapValue05191 : Nat := fullRecordGapCenterValue + 244598

theorem fullRecordGapTerm05191_eq_value :
    recordGapCenter + 244598 = fullRecordGapValue05191 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05191_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05191 (fullRecordGapValue05191 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05191_not_prime : ¬(recordGapCenter + 244598).Prime := by
  rw [fullRecordGapTerm05191_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05191, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05191_fast_pow_mod_ne_one

def fullRecordGapValue05192 : Nat := fullRecordGapCenterValue + 244646

theorem fullRecordGapTerm05192_eq_value :
    recordGapCenter + 244646 = fullRecordGapValue05192 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05192_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05192 (fullRecordGapValue05192 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05192_not_prime : ¬(recordGapCenter + 244646).Prime := by
  rw [fullRecordGapTerm05192_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05192, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05192_fast_pow_mod_ne_one

def fullRecordGapValue05193 : Nat := fullRecordGapCenterValue + 244676

theorem fullRecordGapTerm05193_eq_value :
    recordGapCenter + 244676 = fullRecordGapValue05193 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05193_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05193 (fullRecordGapValue05193 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05193_not_prime : ¬(recordGapCenter + 244676).Prime := by
  rw [fullRecordGapTerm05193_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05193, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05193_fast_pow_mod_ne_one

def fullRecordGapValue05194 : Nat := fullRecordGapCenterValue + 244892

theorem fullRecordGapTerm05194_eq_value :
    recordGapCenter + 244892 = fullRecordGapValue05194 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05194_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05194 (fullRecordGapValue05194 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05194_not_prime : ¬(recordGapCenter + 244892).Prime := by
  rw [fullRecordGapTerm05194_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05194, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05194_fast_pow_mod_ne_one

def fullRecordGapValue05195 : Nat := fullRecordGapCenterValue + 245222

theorem fullRecordGapTerm05195_eq_value :
    recordGapCenter + 245222 = fullRecordGapValue05195 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05195_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05195 (fullRecordGapValue05195 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05195_not_prime : ¬(recordGapCenter + 245222).Prime := by
  rw [fullRecordGapTerm05195_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05195, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05195_fast_pow_mod_ne_one

def fullRecordGapValue05196 : Nat := fullRecordGapCenterValue + 245306

theorem fullRecordGapTerm05196_eq_value :
    recordGapCenter + 245306 = fullRecordGapValue05196 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05196_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05196 (fullRecordGapValue05196 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05196_not_prime : ¬(recordGapCenter + 245306).Prime := by
  rw [fullRecordGapTerm05196_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05196, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05196_fast_pow_mod_ne_one

def fullRecordGapValue05197 : Nat := fullRecordGapCenterValue + 245372

theorem fullRecordGapTerm05197_eq_value :
    recordGapCenter + 245372 = fullRecordGapValue05197 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05197_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05197 (fullRecordGapValue05197 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05197_not_prime : ¬(recordGapCenter + 245372).Prime := by
  rw [fullRecordGapTerm05197_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05197, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05197_fast_pow_mod_ne_one

def fullRecordGapValue05198 : Nat := fullRecordGapCenterValue + 245438

theorem fullRecordGapTerm05198_eq_value :
    recordGapCenter + 245438 = fullRecordGapValue05198 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05198_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05198 (fullRecordGapValue05198 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05198_not_prime : ¬(recordGapCenter + 245438).Prime := by
  rw [fullRecordGapTerm05198_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05198, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05198_fast_pow_mod_ne_one

def fullRecordGapValue05199 : Nat := fullRecordGapCenterValue + 245522

theorem fullRecordGapTerm05199_eq_value :
    recordGapCenter + 245522 = fullRecordGapValue05199 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05199_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05199 (fullRecordGapValue05199 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05199_not_prime : ¬(recordGapCenter + 245522).Prime := by
  rw [fullRecordGapTerm05199_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05199, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05199_fast_pow_mod_ne_one

def fullRecordGapValue05200 : Nat := fullRecordGapCenterValue + 245666

theorem fullRecordGapTerm05200_eq_value :
    recordGapCenter + 245666 = fullRecordGapValue05200 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05200_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05200 (fullRecordGapValue05200 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05200_not_prime : ¬(recordGapCenter + 245666).Prime := by
  rw [fullRecordGapTerm05200_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05200, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05200_fast_pow_mod_ne_one

def fullRecordGapValue05201 : Nat := fullRecordGapCenterValue + 245852

theorem fullRecordGapTerm05201_eq_value :
    recordGapCenter + 245852 = fullRecordGapValue05201 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05201_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05201 (fullRecordGapValue05201 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05201_not_prime : ¬(recordGapCenter + 245852).Prime := by
  rw [fullRecordGapTerm05201_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05201, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05201_fast_pow_mod_ne_one

def fullRecordGapValue05202 : Nat := fullRecordGapCenterValue + 245948

theorem fullRecordGapTerm05202_eq_value :
    recordGapCenter + 245948 = fullRecordGapValue05202 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05202_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05202 (fullRecordGapValue05202 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05202_not_prime : ¬(recordGapCenter + 245948).Prime := by
  rw [fullRecordGapTerm05202_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05202, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05202_fast_pow_mod_ne_one

def fullRecordGapValue05203 : Nat := fullRecordGapCenterValue + 246062

theorem fullRecordGapTerm05203_eq_value :
    recordGapCenter + 246062 = fullRecordGapValue05203 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05203_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05203 (fullRecordGapValue05203 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05203_not_prime : ¬(recordGapCenter + 246062).Prime := by
  rw [fullRecordGapTerm05203_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05203, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05203_fast_pow_mod_ne_one

def fullRecordGapValue05204 : Nat := fullRecordGapCenterValue + 246212

theorem fullRecordGapTerm05204_eq_value :
    recordGapCenter + 246212 = fullRecordGapValue05204 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05204_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05204 (fullRecordGapValue05204 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05204_not_prime : ¬(recordGapCenter + 246212).Prime := by
  rw [fullRecordGapTerm05204_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05204, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05204_fast_pow_mod_ne_one

def fullRecordGapValue05205 : Nat := fullRecordGapCenterValue + 246338

theorem fullRecordGapTerm05205_eq_value :
    recordGapCenter + 246338 = fullRecordGapValue05205 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05205_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05205 (fullRecordGapValue05205 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05205_not_prime : ¬(recordGapCenter + 246338).Prime := by
  rw [fullRecordGapTerm05205_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05205, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05205_fast_pow_mod_ne_one

def fullRecordGapValue05206 : Nat := fullRecordGapCenterValue + 246458

theorem fullRecordGapTerm05206_eq_value :
    recordGapCenter + 246458 = fullRecordGapValue05206 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05206_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05206 (fullRecordGapValue05206 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05206_not_prime : ¬(recordGapCenter + 246458).Prime := by
  rw [fullRecordGapTerm05206_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05206, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05206_fast_pow_mod_ne_one

def fullRecordGapValue05207 : Nat := fullRecordGapCenterValue + 246548

theorem fullRecordGapTerm05207_eq_value :
    recordGapCenter + 246548 = fullRecordGapValue05207 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05207_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05207 (fullRecordGapValue05207 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05207_not_prime : ¬(recordGapCenter + 246548).Prime := by
  rw [fullRecordGapTerm05207_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05207, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05207_fast_pow_mod_ne_one

def fullRecordGapValue05208 : Nat := fullRecordGapCenterValue + 246668

theorem fullRecordGapTerm05208_eq_value :
    recordGapCenter + 246668 = fullRecordGapValue05208 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05208_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05208 (fullRecordGapValue05208 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05208_not_prime : ¬(recordGapCenter + 246668).Prime := by
  rw [fullRecordGapTerm05208_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05208, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05208_fast_pow_mod_ne_one

def fullRecordGapValue05209 : Nat := fullRecordGapCenterValue + 246692

theorem fullRecordGapTerm05209_eq_value :
    recordGapCenter + 246692 = fullRecordGapValue05209 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05209_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05209 (fullRecordGapValue05209 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05209_not_prime : ¬(recordGapCenter + 246692).Prime := by
  rw [fullRecordGapTerm05209_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05209, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05209_fast_pow_mod_ne_one

def fullRecordGapValue05210 : Nat := fullRecordGapCenterValue + 246878

theorem fullRecordGapTerm05210_eq_value :
    recordGapCenter + 246878 = fullRecordGapValue05210 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05210_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05210 (fullRecordGapValue05210 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05210_not_prime : ¬(recordGapCenter + 246878).Prime := by
  rw [fullRecordGapTerm05210_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05210, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05210_fast_pow_mod_ne_one

def fullRecordGapValue05211 : Nat := fullRecordGapCenterValue + 246960

theorem fullRecordGapTerm05211_eq_value :
    recordGapCenter + 246960 = fullRecordGapValue05211 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05211_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05211 (fullRecordGapValue05211 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05211_not_prime : ¬(recordGapCenter + 246960).Prime := by
  rw [fullRecordGapTerm05211_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05211, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05211_fast_pow_mod_ne_one

def fullRecordGapValue05212 : Nat := fullRecordGapCenterValue + 246986

theorem fullRecordGapTerm05212_eq_value :
    recordGapCenter + 246986 = fullRecordGapValue05212 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05212_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05212 (fullRecordGapValue05212 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05212_not_prime : ¬(recordGapCenter + 246986).Prime := by
  rw [fullRecordGapTerm05212_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05212, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05212_fast_pow_mod_ne_one

def fullRecordGapValue05213 : Nat := fullRecordGapCenterValue + 247238

theorem fullRecordGapTerm05213_eq_value :
    recordGapCenter + 247238 = fullRecordGapValue05213 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05213_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05213 (fullRecordGapValue05213 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05213_not_prime : ¬(recordGapCenter + 247238).Prime := by
  rw [fullRecordGapTerm05213_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05213, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05213_fast_pow_mod_ne_one

def fullRecordGapValue05214 : Nat := fullRecordGapCenterValue + 247322

theorem fullRecordGapTerm05214_eq_value :
    recordGapCenter + 247322 = fullRecordGapValue05214 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05214_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05214 (fullRecordGapValue05214 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05214_not_prime : ¬(recordGapCenter + 247322).Prime := by
  rw [fullRecordGapTerm05214_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05214, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05214_fast_pow_mod_ne_one

def fullRecordGapValue05215 : Nat := fullRecordGapCenterValue + 247466

theorem fullRecordGapTerm05215_eq_value :
    recordGapCenter + 247466 = fullRecordGapValue05215 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05215_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05215 (fullRecordGapValue05215 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05215_not_prime : ¬(recordGapCenter + 247466).Prime := by
  rw [fullRecordGapTerm05215_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05215, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05215_fast_pow_mod_ne_one

def fullRecordGapValue05216 : Nat := fullRecordGapCenterValue + 247658

theorem fullRecordGapTerm05216_eq_value :
    recordGapCenter + 247658 = fullRecordGapValue05216 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05216_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05216 (fullRecordGapValue05216 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05216_not_prime : ¬(recordGapCenter + 247658).Prime := by
  rw [fullRecordGapTerm05216_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05216, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05216_fast_pow_mod_ne_one

def fullRecordGapValue05217 : Nat := fullRecordGapCenterValue + 247706

theorem fullRecordGapTerm05217_eq_value :
    recordGapCenter + 247706 = fullRecordGapValue05217 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05217_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05217 (fullRecordGapValue05217 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05217_not_prime : ¬(recordGapCenter + 247706).Prime := by
  rw [fullRecordGapTerm05217_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05217, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05217_fast_pow_mod_ne_one

def fullRecordGapValue05218 : Nat := fullRecordGapCenterValue + 247796

theorem fullRecordGapTerm05218_eq_value :
    recordGapCenter + 247796 = fullRecordGapValue05218 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05218_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05218 (fullRecordGapValue05218 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05218_not_prime : ¬(recordGapCenter + 247796).Prime := by
  rw [fullRecordGapTerm05218_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05218, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05218_fast_pow_mod_ne_one

def fullRecordGapValue05219 : Nat := fullRecordGapCenterValue + 247808

theorem fullRecordGapTerm05219_eq_value :
    recordGapCenter + 247808 = fullRecordGapValue05219 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05219_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05219 (fullRecordGapValue05219 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05219_not_prime : ¬(recordGapCenter + 247808).Prime := by
  rw [fullRecordGapTerm05219_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05219, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05219_fast_pow_mod_ne_one

def fullRecordGapValue05220 : Nat := fullRecordGapCenterValue + 247916

theorem fullRecordGapTerm05220_eq_value :
    recordGapCenter + 247916 = fullRecordGapValue05220 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05220_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05220 (fullRecordGapValue05220 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05220_not_prime : ¬(recordGapCenter + 247916).Prime := by
  rw [fullRecordGapTerm05220_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05220, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05220_fast_pow_mod_ne_one

def fullRecordGapValue05221 : Nat := fullRecordGapCenterValue + 248012

theorem fullRecordGapTerm05221_eq_value :
    recordGapCenter + 248012 = fullRecordGapValue05221 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05221_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05221 (fullRecordGapValue05221 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05221_not_prime : ¬(recordGapCenter + 248012).Prime := by
  rw [fullRecordGapTerm05221_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05221, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05221_fast_pow_mod_ne_one

def fullRecordGapValue05222 : Nat := fullRecordGapCenterValue + 248306

theorem fullRecordGapTerm05222_eq_value :
    recordGapCenter + 248306 = fullRecordGapValue05222 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05222_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05222 (fullRecordGapValue05222 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05222_not_prime : ¬(recordGapCenter + 248306).Prime := by
  rw [fullRecordGapTerm05222_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05222, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05222_fast_pow_mod_ne_one

def fullRecordGapValue05223 : Nat := fullRecordGapCenterValue + 248426

theorem fullRecordGapTerm05223_eq_value :
    recordGapCenter + 248426 = fullRecordGapValue05223 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05223_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05223 (fullRecordGapValue05223 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05223_not_prime : ¬(recordGapCenter + 248426).Prime := by
  rw [fullRecordGapTerm05223_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05223, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05223_fast_pow_mod_ne_one

def fullRecordGapValue05224 : Nat := fullRecordGapCenterValue + 248498

theorem fullRecordGapTerm05224_eq_value :
    recordGapCenter + 248498 = fullRecordGapValue05224 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05224_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05224 (fullRecordGapValue05224 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05224_not_prime : ¬(recordGapCenter + 248498).Prime := by
  rw [fullRecordGapTerm05224_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05224, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05224_fast_pow_mod_ne_one

def fullRecordGapValue05225 : Nat := fullRecordGapCenterValue + 248582

theorem fullRecordGapTerm05225_eq_value :
    recordGapCenter + 248582 = fullRecordGapValue05225 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05225_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05225 (fullRecordGapValue05225 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05225_not_prime : ¬(recordGapCenter + 248582).Prime := by
  rw [fullRecordGapTerm05225_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05225, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05225_fast_pow_mod_ne_one

def fullRecordGapValue05226 : Nat := fullRecordGapCenterValue + 248726

theorem fullRecordGapTerm05226_eq_value :
    recordGapCenter + 248726 = fullRecordGapValue05226 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05226_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05226 (fullRecordGapValue05226 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05226_not_prime : ¬(recordGapCenter + 248726).Prime := by
  rw [fullRecordGapTerm05226_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05226, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05226_fast_pow_mod_ne_one

def fullRecordGapValue05227 : Nat := fullRecordGapCenterValue + 248832

theorem fullRecordGapTerm05227_eq_value :
    recordGapCenter + 248832 = fullRecordGapValue05227 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05227_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05227 (fullRecordGapValue05227 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05227_not_prime : ¬(recordGapCenter + 248832).Prime := by
  rw [fullRecordGapTerm05227_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05227, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05227_fast_pow_mod_ne_one

def fullRecordGapValue05228 : Nat := fullRecordGapCenterValue + 248876

theorem fullRecordGapTerm05228_eq_value :
    recordGapCenter + 248876 = fullRecordGapValue05228 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05228_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05228 (fullRecordGapValue05228 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05228_not_prime : ¬(recordGapCenter + 248876).Prime := by
  rw [fullRecordGapTerm05228_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05228, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05228_fast_pow_mod_ne_one

def fullRecordGapValue05229 : Nat := fullRecordGapCenterValue + 248978

theorem fullRecordGapTerm05229_eq_value :
    recordGapCenter + 248978 = fullRecordGapValue05229 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05229_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05229 (fullRecordGapValue05229 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05229_not_prime : ¬(recordGapCenter + 248978).Prime := by
  rw [fullRecordGapTerm05229_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05229, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05229_fast_pow_mod_ne_one

def fullRecordGapValue05230 : Nat := fullRecordGapCenterValue + 249018

theorem fullRecordGapTerm05230_eq_value :
    recordGapCenter + 249018 = fullRecordGapValue05230 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05230_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05230 (fullRecordGapValue05230 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05230_not_prime : ¬(recordGapCenter + 249018).Prime := by
  rw [fullRecordGapTerm05230_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05230, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05230_fast_pow_mod_ne_one

def fullRecordGapValue05231 : Nat := fullRecordGapCenterValue + 249266

theorem fullRecordGapTerm05231_eq_value :
    recordGapCenter + 249266 = fullRecordGapValue05231 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05231_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05231 (fullRecordGapValue05231 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05231_not_prime : ¬(recordGapCenter + 249266).Prime := by
  rw [fullRecordGapTerm05231_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05231, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05231_fast_pow_mod_ne_one

def fullRecordGapValue05232 : Nat := fullRecordGapCenterValue + 249308

theorem fullRecordGapTerm05232_eq_value :
    recordGapCenter + 249308 = fullRecordGapValue05232 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05232_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05232 (fullRecordGapValue05232 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05232_not_prime : ¬(recordGapCenter + 249308).Prime := by
  rw [fullRecordGapTerm05232_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05232, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05232_fast_pow_mod_ne_one

def fullRecordGapValue05233 : Nat := fullRecordGapCenterValue + 249386

theorem fullRecordGapTerm05233_eq_value :
    recordGapCenter + 249386 = fullRecordGapValue05233 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05233_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05233 (fullRecordGapValue05233 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05233_not_prime : ¬(recordGapCenter + 249386).Prime := by
  rw [fullRecordGapTerm05233_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05233, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05233_fast_pow_mod_ne_one

def fullRecordGapValue05234 : Nat := fullRecordGapCenterValue + 249638

theorem fullRecordGapTerm05234_eq_value :
    recordGapCenter + 249638 = fullRecordGapValue05234 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05234_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05234 (fullRecordGapValue05234 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05234_not_prime : ¬(recordGapCenter + 249638).Prime := by
  rw [fullRecordGapTerm05234_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05234, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05234_fast_pow_mod_ne_one

def fullRecordGapValue05235 : Nat := fullRecordGapCenterValue + 249692

theorem fullRecordGapTerm05235_eq_value :
    recordGapCenter + 249692 = fullRecordGapValue05235 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05235_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05235 (fullRecordGapValue05235 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05235_not_prime : ¬(recordGapCenter + 249692).Prime := by
  rw [fullRecordGapTerm05235_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05235, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05235_fast_pow_mod_ne_one

def fullRecordGapValue05236 : Nat := fullRecordGapCenterValue + 249932

theorem fullRecordGapTerm05236_eq_value :
    recordGapCenter + 249932 = fullRecordGapValue05236 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05236_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05236 (fullRecordGapValue05236 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05236_not_prime : ¬(recordGapCenter + 249932).Prime := by
  rw [fullRecordGapTerm05236_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05236, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05236_fast_pow_mod_ne_one

def fullRecordGapValue05237 : Nat := fullRecordGapCenterValue + 250028

theorem fullRecordGapTerm05237_eq_value :
    recordGapCenter + 250028 = fullRecordGapValue05237 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05237_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05237 (fullRecordGapValue05237 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05237_not_prime : ¬(recordGapCenter + 250028).Prime := by
  rw [fullRecordGapTerm05237_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05237, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05237_fast_pow_mod_ne_one

def fullRecordGapValue05238 : Nat := fullRecordGapCenterValue + 250106

theorem fullRecordGapTerm05238_eq_value :
    recordGapCenter + 250106 = fullRecordGapValue05238 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05238_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05238 (fullRecordGapValue05238 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05238_not_prime : ¬(recordGapCenter + 250106).Prime := by
  rw [fullRecordGapTerm05238_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05238, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05238_fast_pow_mod_ne_one

def fullRecordGapValue05239 : Nat := fullRecordGapCenterValue + 250226

theorem fullRecordGapTerm05239_eq_value :
    recordGapCenter + 250226 = fullRecordGapValue05239 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05239_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05239 (fullRecordGapValue05239 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05239_not_prime : ¬(recordGapCenter + 250226).Prime := by
  rw [fullRecordGapTerm05239_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05239, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05239_fast_pow_mod_ne_one

def fullRecordGapValue05240 : Nat := fullRecordGapCenterValue + 250238

theorem fullRecordGapTerm05240_eq_value :
    recordGapCenter + 250238 = fullRecordGapValue05240 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05240_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05240 (fullRecordGapValue05240 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05240_not_prime : ¬(recordGapCenter + 250238).Prime := by
  rw [fullRecordGapTerm05240_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05240, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05240_fast_pow_mod_ne_one

def fullRecordGapValue05241 : Nat := fullRecordGapCenterValue + 250262

theorem fullRecordGapTerm05241_eq_value :
    recordGapCenter + 250262 = fullRecordGapValue05241 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05241_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05241 (fullRecordGapValue05241 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05241_not_prime : ¬(recordGapCenter + 250262).Prime := by
  rw [fullRecordGapTerm05241_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05241, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05241_fast_pow_mod_ne_one

def fullRecordGapValue05242 : Nat := fullRecordGapCenterValue + 250538

theorem fullRecordGapTerm05242_eq_value :
    recordGapCenter + 250538 = fullRecordGapValue05242 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05242_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05242 (fullRecordGapValue05242 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05242_not_prime : ¬(recordGapCenter + 250538).Prime := by
  rw [fullRecordGapTerm05242_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05242, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05242_fast_pow_mod_ne_one

def fullRecordGapValue05243 : Nat := fullRecordGapCenterValue + 250622

theorem fullRecordGapTerm05243_eq_value :
    recordGapCenter + 250622 = fullRecordGapValue05243 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05243_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05243 (fullRecordGapValue05243 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05243_not_prime : ¬(recordGapCenter + 250622).Prime := by
  rw [fullRecordGapTerm05243_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05243, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05243_fast_pow_mod_ne_one

def fullRecordGapValue05244 : Nat := fullRecordGapCenterValue + 250658

theorem fullRecordGapTerm05244_eq_value :
    recordGapCenter + 250658 = fullRecordGapValue05244 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05244_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05244 (fullRecordGapValue05244 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05244_not_prime : ¬(recordGapCenter + 250658).Prime := by
  rw [fullRecordGapTerm05244_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05244, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05244_fast_pow_mod_ne_one

def fullRecordGapValue05245 : Nat := fullRecordGapCenterValue + 250742

theorem fullRecordGapTerm05245_eq_value :
    recordGapCenter + 250742 = fullRecordGapValue05245 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05245_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05245 (fullRecordGapValue05245 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05245_not_prime : ¬(recordGapCenter + 250742).Prime := by
  rw [fullRecordGapTerm05245_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05245, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05245_fast_pow_mod_ne_one

def fullRecordGapValue05246 : Nat := fullRecordGapCenterValue + 250748

theorem fullRecordGapTerm05246_eq_value :
    recordGapCenter + 250748 = fullRecordGapValue05246 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05246_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05246 (fullRecordGapValue05246 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05246_not_prime : ¬(recordGapCenter + 250748).Prime := by
  rw [fullRecordGapTerm05246_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05246, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05246_fast_pow_mod_ne_one

def fullRecordGapValue05247 : Nat := fullRecordGapCenterValue + 250880

theorem fullRecordGapTerm05247_eq_value :
    recordGapCenter + 250880 = fullRecordGapValue05247 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05247_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05247 (fullRecordGapValue05247 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05247_not_prime : ¬(recordGapCenter + 250880).Prime := by
  rw [fullRecordGapTerm05247_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05247, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05247_fast_pow_mod_ne_one

def fullRecordGapValue05248 : Nat := fullRecordGapCenterValue + 250892

theorem fullRecordGapTerm05248_eq_value :
    recordGapCenter + 250892 = fullRecordGapValue05248 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05248_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05248 (fullRecordGapValue05248 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05248_not_prime : ¬(recordGapCenter + 250892).Prime := by
  rw [fullRecordGapTerm05248_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05248, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05248_fast_pow_mod_ne_one

def fullRecordGapValue05249 : Nat := fullRecordGapCenterValue + 251102

theorem fullRecordGapTerm05249_eq_value :
    recordGapCenter + 251102 = fullRecordGapValue05249 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05249_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05249 (fullRecordGapValue05249 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05249_not_prime : ¬(recordGapCenter + 251102).Prime := by
  rw [fullRecordGapTerm05249_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05249, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05249_fast_pow_mod_ne_one

def fullRecordGapValue05250 : Nat := fullRecordGapCenterValue + 251276

theorem fullRecordGapTerm05250_eq_value :
    recordGapCenter + 251276 = fullRecordGapValue05250 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05250_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05250 (fullRecordGapValue05250 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05250_not_prime : ¬(recordGapCenter + 251276).Prime := by
  rw [fullRecordGapTerm05250_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05250, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05250_fast_pow_mod_ne_one

def fullRecordGapValue05251 : Nat := fullRecordGapCenterValue + 251318

theorem fullRecordGapTerm05251_eq_value :
    recordGapCenter + 251318 = fullRecordGapValue05251 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05251_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05251 (fullRecordGapValue05251 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05251_not_prime : ¬(recordGapCenter + 251318).Prime := by
  rw [fullRecordGapTerm05251_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05251, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05251_fast_pow_mod_ne_one

def fullRecordGapValue05252 : Nat := fullRecordGapCenterValue + 251366

theorem fullRecordGapTerm05252_eq_value :
    recordGapCenter + 251366 = fullRecordGapValue05252 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05252_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05252 (fullRecordGapValue05252 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05252_not_prime : ¬(recordGapCenter + 251366).Prime := by
  rw [fullRecordGapTerm05252_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05252, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05252_fast_pow_mod_ne_one

def fullRecordGapValue05253 : Nat := fullRecordGapCenterValue + 251462

theorem fullRecordGapTerm05253_eq_value :
    recordGapCenter + 251462 = fullRecordGapValue05253 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05253_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05253 (fullRecordGapValue05253 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05253_not_prime : ¬(recordGapCenter + 251462).Prime := by
  rw [fullRecordGapTerm05253_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05253, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05253_fast_pow_mod_ne_one

def fullRecordGapValue05254 : Nat := fullRecordGapCenterValue + 251492

theorem fullRecordGapTerm05254_eq_value :
    recordGapCenter + 251492 = fullRecordGapValue05254 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05254_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05254 (fullRecordGapValue05254 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05254_not_prime : ¬(recordGapCenter + 251492).Prime := by
  rw [fullRecordGapTerm05254_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05254, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05254_fast_pow_mod_ne_one

def fullRecordGapValue05255 : Nat := fullRecordGapCenterValue + 251606

theorem fullRecordGapTerm05255_eq_value :
    recordGapCenter + 251606 = fullRecordGapValue05255 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05255_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05255 (fullRecordGapValue05255 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05255_not_prime : ¬(recordGapCenter + 251606).Prime := by
  rw [fullRecordGapTerm05255_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05255, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05255_fast_pow_mod_ne_one

def fullRecordGapValue05256 : Nat := fullRecordGapCenterValue + 251708

theorem fullRecordGapTerm05256_eq_value :
    recordGapCenter + 251708 = fullRecordGapValue05256 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05256_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05256 (fullRecordGapValue05256 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05256_not_prime : ¬(recordGapCenter + 251708).Prime := by
  rw [fullRecordGapTerm05256_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05256, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05256_fast_pow_mod_ne_one

def fullRecordGapValue05257 : Nat := fullRecordGapCenterValue + 251798

theorem fullRecordGapTerm05257_eq_value :
    recordGapCenter + 251798 = fullRecordGapValue05257 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05257_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05257 (fullRecordGapValue05257 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05257_not_prime : ¬(recordGapCenter + 251798).Prime := by
  rw [fullRecordGapTerm05257_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05257, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05257_fast_pow_mod_ne_one

def fullRecordGapValue05258 : Nat := fullRecordGapCenterValue + 251858

theorem fullRecordGapTerm05258_eq_value :
    recordGapCenter + 251858 = fullRecordGapValue05258 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05258_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05258 (fullRecordGapValue05258 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05258_not_prime : ¬(recordGapCenter + 251858).Prime := by
  rw [fullRecordGapTerm05258_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05258, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05258_fast_pow_mod_ne_one

def fullRecordGapValue05259 : Nat := fullRecordGapCenterValue + 251876

theorem fullRecordGapTerm05259_eq_value :
    recordGapCenter + 251876 = fullRecordGapValue05259 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05259_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05259 (fullRecordGapValue05259 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05259_not_prime : ¬(recordGapCenter + 251876).Prime := by
  rw [fullRecordGapTerm05259_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05259, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05259_fast_pow_mod_ne_one

def fullRecordGapValue05260 : Nat := fullRecordGapCenterValue + 252000

theorem fullRecordGapTerm05260_eq_value :
    recordGapCenter + 252000 = fullRecordGapValue05260 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05260_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05260 (fullRecordGapValue05260 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05260_not_prime : ¬(recordGapCenter + 252000).Prime := by
  rw [fullRecordGapTerm05260_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05260, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05260_fast_pow_mod_ne_one

def fullRecordGapValue05261 : Nat := fullRecordGapCenterValue + 252158

theorem fullRecordGapTerm05261_eq_value :
    recordGapCenter + 252158 = fullRecordGapValue05261 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05261_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05261 (fullRecordGapValue05261 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05261_not_prime : ¬(recordGapCenter + 252158).Prime := by
  rw [fullRecordGapTerm05261_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05261, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05261_fast_pow_mod_ne_one

def fullRecordGapValue05262 : Nat := fullRecordGapCenterValue + 252302

theorem fullRecordGapTerm05262_eq_value :
    recordGapCenter + 252302 = fullRecordGapValue05262 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05262_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05262 (fullRecordGapValue05262 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05262_not_prime : ¬(recordGapCenter + 252302).Prime := by
  rw [fullRecordGapTerm05262_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05262, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05262_fast_pow_mod_ne_one

def fullRecordGapValue05263 : Nat := fullRecordGapCenterValue + 252542

theorem fullRecordGapTerm05263_eq_value :
    recordGapCenter + 252542 = fullRecordGapValue05263 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05263_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05263 (fullRecordGapValue05263 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05263_not_prime : ¬(recordGapCenter + 252542).Prime := by
  rw [fullRecordGapTerm05263_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05263, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05263_fast_pow_mod_ne_one

def fullRecordGapValue05264 : Nat := fullRecordGapCenterValue + 252698

theorem fullRecordGapTerm05264_eq_value :
    recordGapCenter + 252698 = fullRecordGapValue05264 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05264_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05264 (fullRecordGapValue05264 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05264_not_prime : ¬(recordGapCenter + 252698).Prime := by
  rw [fullRecordGapTerm05264_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05264, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05264_fast_pow_mod_ne_one

def fullRecordGapValue05265 : Nat := fullRecordGapCenterValue + 252716

theorem fullRecordGapTerm05265_eq_value :
    recordGapCenter + 252716 = fullRecordGapValue05265 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05265_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05265 (fullRecordGapValue05265 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05265_not_prime : ¬(recordGapCenter + 252716).Prime := by
  rw [fullRecordGapTerm05265_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05265, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05265_fast_pow_mod_ne_one

def fullRecordGapValue05266 : Nat := fullRecordGapCenterValue + 252788

theorem fullRecordGapTerm05266_eq_value :
    recordGapCenter + 252788 = fullRecordGapValue05266 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05266_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05266 (fullRecordGapValue05266 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05266_not_prime : ¬(recordGapCenter + 252788).Prime := by
  rw [fullRecordGapTerm05266_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05266, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05266_fast_pow_mod_ne_one

def fullRecordGapValue05267 : Nat := fullRecordGapCenterValue + 252962

theorem fullRecordGapTerm05267_eq_value :
    recordGapCenter + 252962 = fullRecordGapValue05267 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05267_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05267 (fullRecordGapValue05267 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05267_not_prime : ¬(recordGapCenter + 252962).Prime := by
  rw [fullRecordGapTerm05267_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05267, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05267_fast_pow_mod_ne_one

def fullRecordGapValue05268 : Nat := fullRecordGapCenterValue + 253082

theorem fullRecordGapTerm05268_eq_value :
    recordGapCenter + 253082 = fullRecordGapValue05268 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05268_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05268 (fullRecordGapValue05268 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05268_not_prime : ¬(recordGapCenter + 253082).Prime := by
  rw [fullRecordGapTerm05268_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05268, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05268_fast_pow_mod_ne_one

def fullRecordGapValue05269 : Nat := fullRecordGapCenterValue + 253262

theorem fullRecordGapTerm05269_eq_value :
    recordGapCenter + 253262 = fullRecordGapValue05269 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05269_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05269 (fullRecordGapValue05269 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05269_not_prime : ¬(recordGapCenter + 253262).Prime := by
  rw [fullRecordGapTerm05269_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05269, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05269_fast_pow_mod_ne_one

def fullRecordGapValue05270 : Nat := fullRecordGapCenterValue + 253268

theorem fullRecordGapTerm05270_eq_value :
    recordGapCenter + 253268 = fullRecordGapValue05270 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05270_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05270 (fullRecordGapValue05270 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05270_not_prime : ¬(recordGapCenter + 253268).Prime := by
  rw [fullRecordGapTerm05270_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05270, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05270_fast_pow_mod_ne_one

def fullRecordGapValue05271 : Nat := fullRecordGapCenterValue + 253382

theorem fullRecordGapTerm05271_eq_value :
    recordGapCenter + 253382 = fullRecordGapValue05271 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05271_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05271 (fullRecordGapValue05271 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05271_not_prime : ¬(recordGapCenter + 253382).Prime := by
  rw [fullRecordGapTerm05271_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05271, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05271_fast_pow_mod_ne_one

def fullRecordGapValue05272 : Nat := fullRecordGapCenterValue + 253440

theorem fullRecordGapTerm05272_eq_value :
    recordGapCenter + 253440 = fullRecordGapValue05272 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05272_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05272 (fullRecordGapValue05272 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05272_not_prime : ¬(recordGapCenter + 253440).Prime := by
  rw [fullRecordGapTerm05272_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05272, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05272_fast_pow_mod_ne_one

def fullRecordGapValue05273 : Nat := fullRecordGapCenterValue + 253466

theorem fullRecordGapTerm05273_eq_value :
    recordGapCenter + 253466 = fullRecordGapValue05273 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05273_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05273 (fullRecordGapValue05273 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05273_not_prime : ¬(recordGapCenter + 253466).Prime := by
  rw [fullRecordGapTerm05273_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05273, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05273_fast_pow_mod_ne_one

def fullRecordGapValue05274 : Nat := fullRecordGapCenterValue + 253508

theorem fullRecordGapTerm05274_eq_value :
    recordGapCenter + 253508 = fullRecordGapValue05274 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05274_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05274 (fullRecordGapValue05274 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05274_not_prime : ¬(recordGapCenter + 253508).Prime := by
  rw [fullRecordGapTerm05274_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05274, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05274_fast_pow_mod_ne_one

def fullRecordGapValue05275 : Nat := fullRecordGapCenterValue + 253646

theorem fullRecordGapTerm05275_eq_value :
    recordGapCenter + 253646 = fullRecordGapValue05275 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05275_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05275 (fullRecordGapValue05275 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05275_not_prime : ¬(recordGapCenter + 253646).Prime := by
  rw [fullRecordGapTerm05275_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05275, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05275_fast_pow_mod_ne_one

def fullRecordGapValue05276 : Nat := fullRecordGapCenterValue + 253718

theorem fullRecordGapTerm05276_eq_value :
    recordGapCenter + 253718 = fullRecordGapValue05276 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05276_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05276 (fullRecordGapValue05276 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05276_not_prime : ¬(recordGapCenter + 253718).Prime := by
  rw [fullRecordGapTerm05276_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05276, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05276_fast_pow_mod_ne_one

def fullRecordGapValue05277 : Nat := fullRecordGapCenterValue + 253772

theorem fullRecordGapTerm05277_eq_value :
    recordGapCenter + 253772 = fullRecordGapValue05277 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05277_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05277 (fullRecordGapValue05277 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05277_not_prime : ¬(recordGapCenter + 253772).Prime := by
  rw [fullRecordGapTerm05277_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05277, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05277_fast_pow_mod_ne_one

def fullRecordGapValue05278 : Nat := fullRecordGapCenterValue + 254016

theorem fullRecordGapTerm05278_eq_value :
    recordGapCenter + 254016 = fullRecordGapValue05278 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05278_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05278 (fullRecordGapValue05278 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05278_not_prime : ¬(recordGapCenter + 254016).Prime := by
  rw [fullRecordGapTerm05278_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05278, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05278_fast_pow_mod_ne_one

def fullRecordGapValue05279 : Nat := fullRecordGapCenterValue + 254100

theorem fullRecordGapTerm05279_eq_value :
    recordGapCenter + 254100 = fullRecordGapValue05279 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05279_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05279 (fullRecordGapValue05279 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05279_not_prime : ¬(recordGapCenter + 254100).Prime := by
  rw [fullRecordGapTerm05279_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05279, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05279_fast_pow_mod_ne_one

def fullRecordGapValue05280 : Nat := fullRecordGapCenterValue + 254102

theorem fullRecordGapTerm05280_eq_value :
    recordGapCenter + 254102 = fullRecordGapValue05280 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05280_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05280 (fullRecordGapValue05280 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05280_not_prime : ¬(recordGapCenter + 254102).Prime := by
  rw [fullRecordGapTerm05280_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05280, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05280_fast_pow_mod_ne_one

def fullRecordGapValue05281 : Nat := fullRecordGapCenterValue + 254132

theorem fullRecordGapTerm05281_eq_value :
    recordGapCenter + 254132 = fullRecordGapValue05281 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05281_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05281 (fullRecordGapValue05281 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05281_not_prime : ¬(recordGapCenter + 254132).Prime := by
  rw [fullRecordGapTerm05281_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05281, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05281_fast_pow_mod_ne_one

def fullRecordGapValue05282 : Nat := fullRecordGapCenterValue + 254348

theorem fullRecordGapTerm05282_eq_value :
    recordGapCenter + 254348 = fullRecordGapValue05282 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05282_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05282 (fullRecordGapValue05282 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05282_not_prime : ¬(recordGapCenter + 254348).Prime := by
  rw [fullRecordGapTerm05282_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05282, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05282_fast_pow_mod_ne_one

def fullRecordGapValue05283 : Nat := fullRecordGapCenterValue + 254396

theorem fullRecordGapTerm05283_eq_value :
    recordGapCenter + 254396 = fullRecordGapValue05283 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05283_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05283 (fullRecordGapValue05283 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05283_not_prime : ¬(recordGapCenter + 254396).Prime := by
  rw [fullRecordGapTerm05283_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05283, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05283_fast_pow_mod_ne_one

def fullRecordGapValue05284 : Nat := fullRecordGapCenterValue + 254522

theorem fullRecordGapTerm05284_eq_value :
    recordGapCenter + 254522 = fullRecordGapValue05284 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05284_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05284 (fullRecordGapValue05284 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05284_not_prime : ¬(recordGapCenter + 254522).Prime := by
  rw [fullRecordGapTerm05284_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05284, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05284_fast_pow_mod_ne_one

def fullRecordGapValue05285 : Nat := fullRecordGapCenterValue + 254588

theorem fullRecordGapTerm05285_eq_value :
    recordGapCenter + 254588 = fullRecordGapValue05285 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05285_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05285 (fullRecordGapValue05285 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05285_not_prime : ¬(recordGapCenter + 254588).Prime := by
  rw [fullRecordGapTerm05285_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05285, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05285_fast_pow_mod_ne_one

def fullRecordGapValue05286 : Nat := fullRecordGapCenterValue + 254906

theorem fullRecordGapTerm05286_eq_value :
    recordGapCenter + 254906 = fullRecordGapValue05286 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05286_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05286 (fullRecordGapValue05286 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05286_not_prime : ¬(recordGapCenter + 254906).Prime := by
  rw [fullRecordGapTerm05286_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05286, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05286_fast_pow_mod_ne_one

def fullRecordGapValue05287 : Nat := fullRecordGapCenterValue + 254948

theorem fullRecordGapTerm05287_eq_value :
    recordGapCenter + 254948 = fullRecordGapValue05287 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05287_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05287 (fullRecordGapValue05287 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05287_not_prime : ¬(recordGapCenter + 254948).Prime := by
  rw [fullRecordGapTerm05287_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05287, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05287_fast_pow_mod_ne_one

def fullRecordGapValue05288 : Nat := fullRecordGapCenterValue + 254972

theorem fullRecordGapTerm05288_eq_value :
    recordGapCenter + 254972 = fullRecordGapValue05288 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05288_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05288 (fullRecordGapValue05288 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05288_not_prime : ¬(recordGapCenter + 254972).Prime := by
  rw [fullRecordGapTerm05288_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05288, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05288_fast_pow_mod_ne_one

def fullRecordGapValue05289 : Nat := fullRecordGapCenterValue + 255092

theorem fullRecordGapTerm05289_eq_value :
    recordGapCenter + 255092 = fullRecordGapValue05289 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05289_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05289 (fullRecordGapValue05289 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05289_not_prime : ¬(recordGapCenter + 255092).Prime := by
  rw [fullRecordGapTerm05289_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05289, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05289_fast_pow_mod_ne_one

def fullRecordGapValue05290 : Nat := fullRecordGapCenterValue + 255182

theorem fullRecordGapTerm05290_eq_value :
    recordGapCenter + 255182 = fullRecordGapValue05290 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05290_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05290 (fullRecordGapValue05290 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05290_not_prime : ¬(recordGapCenter + 255182).Prime := by
  rw [fullRecordGapTerm05290_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05290, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05290_fast_pow_mod_ne_one

def fullRecordGapValue05291 : Nat := fullRecordGapCenterValue + 255428

theorem fullRecordGapTerm05291_eq_value :
    recordGapCenter + 255428 = fullRecordGapValue05291 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05291_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05291 (fullRecordGapValue05291 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05291_not_prime : ¬(recordGapCenter + 255428).Prime := by
  rw [fullRecordGapTerm05291_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05291, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05291_fast_pow_mod_ne_one

def fullRecordGapValue05292 : Nat := fullRecordGapCenterValue + 255452

theorem fullRecordGapTerm05292_eq_value :
    recordGapCenter + 255452 = fullRecordGapValue05292 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05292_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05292 (fullRecordGapValue05292 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05292_not_prime : ¬(recordGapCenter + 255452).Prime := by
  rw [fullRecordGapTerm05292_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05292, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05292_fast_pow_mod_ne_one

def fullRecordGapValue05293 : Nat := fullRecordGapCenterValue + 255686

theorem fullRecordGapTerm05293_eq_value :
    recordGapCenter + 255686 = fullRecordGapValue05293 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05293_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05293 (fullRecordGapValue05293 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05293_not_prime : ¬(recordGapCenter + 255686).Prime := by
  rw [fullRecordGapTerm05293_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05293, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05293_fast_pow_mod_ne_one

def fullRecordGapValue05294 : Nat := fullRecordGapCenterValue + 255902

theorem fullRecordGapTerm05294_eq_value :
    recordGapCenter + 255902 = fullRecordGapValue05294 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05294_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05294 (fullRecordGapValue05294 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05294_not_prime : ¬(recordGapCenter + 255902).Prime := by
  rw [fullRecordGapTerm05294_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05294, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05294_fast_pow_mod_ne_one

def fullRecordGapValue05295 : Nat := fullRecordGapCenterValue + 255908

theorem fullRecordGapTerm05295_eq_value :
    recordGapCenter + 255908 = fullRecordGapValue05295 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05295_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05295 (fullRecordGapValue05295 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05295_not_prime : ¬(recordGapCenter + 255908).Prime := by
  rw [fullRecordGapTerm05295_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05295, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05295_fast_pow_mod_ne_one

def fullRecordGapValue05296 : Nat := fullRecordGapCenterValue + 256028

theorem fullRecordGapTerm05296_eq_value :
    recordGapCenter + 256028 = fullRecordGapValue05296 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05296_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05296 (fullRecordGapValue05296 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05296_not_prime : ¬(recordGapCenter + 256028).Prime := by
  rw [fullRecordGapTerm05296_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05296, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05296_fast_pow_mod_ne_one

def fullRecordGapValue05297 : Nat := fullRecordGapCenterValue + 256148

theorem fullRecordGapTerm05297_eq_value :
    recordGapCenter + 256148 = fullRecordGapValue05297 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05297_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05297 (fullRecordGapValue05297 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05297_not_prime : ¬(recordGapCenter + 256148).Prime := by
  rw [fullRecordGapTerm05297_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05297, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05297_fast_pow_mod_ne_one

def fullRecordGapValue05298 : Nat := fullRecordGapCenterValue + 256226

theorem fullRecordGapTerm05298_eq_value :
    recordGapCenter + 256226 = fullRecordGapValue05298 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05298_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05298 (fullRecordGapValue05298 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05298_not_prime : ¬(recordGapCenter + 256226).Prime := by
  rw [fullRecordGapTerm05298_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05298, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05298_fast_pow_mod_ne_one

def fullRecordGapValue05299 : Nat := fullRecordGapCenterValue + 256268

theorem fullRecordGapTerm05299_eq_value :
    recordGapCenter + 256268 = fullRecordGapValue05299 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05299_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05299 (fullRecordGapValue05299 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05299_not_prime : ¬(recordGapCenter + 256268).Prime := by
  rw [fullRecordGapTerm05299_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05299, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05299_fast_pow_mod_ne_one

def fullRecordGapValue05300 : Nat := fullRecordGapCenterValue + 256436

theorem fullRecordGapTerm05300_eq_value :
    recordGapCenter + 256436 = fullRecordGapValue05300 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05300_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05300 (fullRecordGapValue05300 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05300_not_prime : ¬(recordGapCenter + 256436).Prime := by
  rw [fullRecordGapTerm05300_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05300, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05300_fast_pow_mod_ne_one

def fullRecordGapValue05301 : Nat := fullRecordGapCenterValue + 256478

theorem fullRecordGapTerm05301_eq_value :
    recordGapCenter + 256478 = fullRecordGapValue05301 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05301_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05301 (fullRecordGapValue05301 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05301_not_prime : ¬(recordGapCenter + 256478).Prime := by
  rw [fullRecordGapTerm05301_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05301, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05301_fast_pow_mod_ne_one

def fullRecordGapValue05302 : Nat := fullRecordGapCenterValue + 256608

theorem fullRecordGapTerm05302_eq_value :
    recordGapCenter + 256608 = fullRecordGapValue05302 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05302_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05302 (fullRecordGapValue05302 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05302_not_prime : ¬(recordGapCenter + 256608).Prime := by
  rw [fullRecordGapTerm05302_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05302, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05302_fast_pow_mod_ne_one

def fullRecordGapValue05303 : Nat := fullRecordGapCenterValue + 256628

theorem fullRecordGapTerm05303_eq_value :
    recordGapCenter + 256628 = fullRecordGapValue05303 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05303_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05303 (fullRecordGapValue05303 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05303_not_prime : ¬(recordGapCenter + 256628).Prime := by
  rw [fullRecordGapTerm05303_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05303, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05303_fast_pow_mod_ne_one

def fullRecordGapValue05304 : Nat := fullRecordGapCenterValue + 256826

theorem fullRecordGapTerm05304_eq_value :
    recordGapCenter + 256826 = fullRecordGapValue05304 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05304_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05304 (fullRecordGapValue05304 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05304_not_prime : ¬(recordGapCenter + 256826).Prime := by
  rw [fullRecordGapTerm05304_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05304, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05304_fast_pow_mod_ne_one

def fullRecordGapValue05305 : Nat := fullRecordGapCenterValue + 256862

theorem fullRecordGapTerm05305_eq_value :
    recordGapCenter + 256862 = fullRecordGapValue05305 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05305_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05305 (fullRecordGapValue05305 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05305_not_prime : ¬(recordGapCenter + 256862).Prime := by
  rw [fullRecordGapTerm05305_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05305, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05305_fast_pow_mod_ne_one

def fullRecordGapValue05306 : Nat := fullRecordGapCenterValue + 256898

theorem fullRecordGapTerm05306_eq_value :
    recordGapCenter + 256898 = fullRecordGapValue05306 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05306_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05306 (fullRecordGapValue05306 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05306_not_prime : ¬(recordGapCenter + 256898).Prime := by
  rw [fullRecordGapTerm05306_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05306, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05306_fast_pow_mod_ne_one

def fullRecordGapValue05307 : Nat := fullRecordGapCenterValue + 256922

theorem fullRecordGapTerm05307_eq_value :
    recordGapCenter + 256922 = fullRecordGapValue05307 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05307_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05307 (fullRecordGapValue05307 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05307_not_prime : ¬(recordGapCenter + 256922).Prime := by
  rw [fullRecordGapTerm05307_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05307, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05307_fast_pow_mod_ne_one

def fullRecordGapValue05308 : Nat := fullRecordGapCenterValue + 256946

theorem fullRecordGapTerm05308_eq_value :
    recordGapCenter + 256946 = fullRecordGapValue05308 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05308_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05308 (fullRecordGapValue05308 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05308_not_prime : ¬(recordGapCenter + 256946).Prime := by
  rw [fullRecordGapTerm05308_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05308, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05308_fast_pow_mod_ne_one

def fullRecordGapValue05309 : Nat := fullRecordGapCenterValue + 257126

theorem fullRecordGapTerm05309_eq_value :
    recordGapCenter + 257126 = fullRecordGapValue05309 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05309_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05309 (fullRecordGapValue05309 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05309_not_prime : ¬(recordGapCenter + 257126).Prime := by
  rw [fullRecordGapTerm05309_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05309, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05309_fast_pow_mod_ne_one

def fullRecordGapValue05310 : Nat := fullRecordGapCenterValue + 257250

theorem fullRecordGapTerm05310_eq_value :
    recordGapCenter + 257250 = fullRecordGapValue05310 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05310_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05310 (fullRecordGapValue05310 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05310_not_prime : ¬(recordGapCenter + 257250).Prime := by
  rw [fullRecordGapTerm05310_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05310, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05310_fast_pow_mod_ne_one

def fullRecordGapValue05311 : Nat := fullRecordGapCenterValue + 257366

theorem fullRecordGapTerm05311_eq_value :
    recordGapCenter + 257366 = fullRecordGapValue05311 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05311_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05311 (fullRecordGapValue05311 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05311_not_prime : ¬(recordGapCenter + 257366).Prime := by
  rw [fullRecordGapTerm05311_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05311, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05311_fast_pow_mod_ne_one

def fullRecordGapValue05312 : Nat := fullRecordGapCenterValue + 257612

theorem fullRecordGapTerm05312_eq_value :
    recordGapCenter + 257612 = fullRecordGapValue05312 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05312_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05312 (fullRecordGapValue05312 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05312_not_prime : ¬(recordGapCenter + 257612).Prime := by
  rw [fullRecordGapTerm05312_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05312, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05312_fast_pow_mod_ne_one

def fullRecordGapValue05313 : Nat := fullRecordGapCenterValue + 257666

theorem fullRecordGapTerm05313_eq_value :
    recordGapCenter + 257666 = fullRecordGapValue05313 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05313_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05313 (fullRecordGapValue05313 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05313_not_prime : ¬(recordGapCenter + 257666).Prime := by
  rw [fullRecordGapTerm05313_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05313, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05313_fast_pow_mod_ne_one

def fullRecordGapValue05314 : Nat := fullRecordGapCenterValue + 257918

theorem fullRecordGapTerm05314_eq_value :
    recordGapCenter + 257918 = fullRecordGapValue05314 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05314_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05314 (fullRecordGapValue05314 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05314_not_prime : ¬(recordGapCenter + 257918).Prime := by
  rw [fullRecordGapTerm05314_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05314, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05314_fast_pow_mod_ne_one

def fullRecordGapValue05315 : Nat := fullRecordGapCenterValue + 258002

theorem fullRecordGapTerm05315_eq_value :
    recordGapCenter + 258002 = fullRecordGapValue05315 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05315_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05315 (fullRecordGapValue05315 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05315_not_prime : ¬(recordGapCenter + 258002).Prime := by
  rw [fullRecordGapTerm05315_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05315, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05315_fast_pow_mod_ne_one

def fullRecordGapValue05316 : Nat := fullRecordGapCenterValue + 258338

theorem fullRecordGapTerm05316_eq_value :
    recordGapCenter + 258338 = fullRecordGapValue05316 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05316_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05316 (fullRecordGapValue05316 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05316_not_prime : ¬(recordGapCenter + 258338).Prime := by
  rw [fullRecordGapTerm05316_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05316, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05316_fast_pow_mod_ne_one

def fullRecordGapValue05317 : Nat := fullRecordGapCenterValue + 258578

theorem fullRecordGapTerm05317_eq_value :
    recordGapCenter + 258578 = fullRecordGapValue05317 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05317_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05317 (fullRecordGapValue05317 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05317_not_prime : ¬(recordGapCenter + 258578).Prime := by
  rw [fullRecordGapTerm05317_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05317, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05317_fast_pow_mod_ne_one

def fullRecordGapValue05318 : Nat := fullRecordGapCenterValue + 258668

theorem fullRecordGapTerm05318_eq_value :
    recordGapCenter + 258668 = fullRecordGapValue05318 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05318_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05318 (fullRecordGapValue05318 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05318_not_prime : ¬(recordGapCenter + 258668).Prime := by
  rw [fullRecordGapTerm05318_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05318, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05318_fast_pow_mod_ne_one

def fullRecordGapValue05319 : Nat := fullRecordGapCenterValue + 258798

theorem fullRecordGapTerm05319_eq_value :
    recordGapCenter + 258798 = fullRecordGapValue05319 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05319_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05319 (fullRecordGapValue05319 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05319_not_prime : ¬(recordGapCenter + 258798).Prime := by
  rw [fullRecordGapTerm05319_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05319, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05319_fast_pow_mod_ne_one

def fullRecordGapValue05320 : Nat := fullRecordGapCenterValue + 258806

theorem fullRecordGapTerm05320_eq_value :
    recordGapCenter + 258806 = fullRecordGapValue05320 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05320_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05320 (fullRecordGapValue05320 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05320_not_prime : ¬(recordGapCenter + 258806).Prime := by
  rw [fullRecordGapTerm05320_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05320, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05320_fast_pow_mod_ne_one

def fullRecordGapValue05321 : Nat := fullRecordGapCenterValue + 258878

theorem fullRecordGapTerm05321_eq_value :
    recordGapCenter + 258878 = fullRecordGapValue05321 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05321_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05321 (fullRecordGapValue05321 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05321_not_prime : ¬(recordGapCenter + 258878).Prime := by
  rw [fullRecordGapTerm05321_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05321, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05321_fast_pow_mod_ne_one

def fullRecordGapValue05322 : Nat := fullRecordGapCenterValue + 259058

theorem fullRecordGapTerm05322_eq_value :
    recordGapCenter + 259058 = fullRecordGapValue05322 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05322_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05322 (fullRecordGapValue05322 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05322_not_prime : ¬(recordGapCenter + 259058).Prime := by
  rw [fullRecordGapTerm05322_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05322, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05322_fast_pow_mod_ne_one

def fullRecordGapValue05323 : Nat := fullRecordGapCenterValue + 259106

theorem fullRecordGapTerm05323_eq_value :
    recordGapCenter + 259106 = fullRecordGapValue05323 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05323_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05323 (fullRecordGapValue05323 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05323_not_prime : ¬(recordGapCenter + 259106).Prime := by
  rw [fullRecordGapTerm05323_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05323, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05323_fast_pow_mod_ne_one

def fullRecordGapValue05324 : Nat := fullRecordGapCenterValue + 259206

theorem fullRecordGapTerm05324_eq_value :
    recordGapCenter + 259206 = fullRecordGapValue05324 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05324_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05324 (fullRecordGapValue05324 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05324_not_prime : ¬(recordGapCenter + 259206).Prime := by
  rw [fullRecordGapTerm05324_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05324, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05324_fast_pow_mod_ne_one

def fullRecordGapValue05325 : Nat := fullRecordGapCenterValue + 259268

theorem fullRecordGapTerm05325_eq_value :
    recordGapCenter + 259268 = fullRecordGapValue05325 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05325_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05325 (fullRecordGapValue05325 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05325_not_prime : ¬(recordGapCenter + 259268).Prime := by
  rw [fullRecordGapTerm05325_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05325, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05325_fast_pow_mod_ne_one

def fullRecordGapValue05326 : Nat := fullRecordGapCenterValue + 259308

theorem fullRecordGapTerm05326_eq_value :
    recordGapCenter + 259308 = fullRecordGapValue05326 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05326_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05326 (fullRecordGapValue05326 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05326_not_prime : ¬(recordGapCenter + 259308).Prime := by
  rw [fullRecordGapTerm05326_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05326, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05326_fast_pow_mod_ne_one

def fullRecordGapValue05327 : Nat := fullRecordGapCenterValue + 259466

theorem fullRecordGapTerm05327_eq_value :
    recordGapCenter + 259466 = fullRecordGapValue05327 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05327_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05327 (fullRecordGapValue05327 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05327_not_prime : ¬(recordGapCenter + 259466).Prime := by
  rw [fullRecordGapTerm05327_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05327, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05327_fast_pow_mod_ne_one

def fullRecordGapValue05328 : Nat := fullRecordGapCenterValue + 259626

theorem fullRecordGapTerm05328_eq_value :
    recordGapCenter + 259626 = fullRecordGapValue05328 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05328_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05328 (fullRecordGapValue05328 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05328_not_prime : ¬(recordGapCenter + 259626).Prime := by
  rw [fullRecordGapTerm05328_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05328, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05328_fast_pow_mod_ne_one

def fullRecordGapValue05329 : Nat := fullRecordGapCenterValue + 259682

theorem fullRecordGapTerm05329_eq_value :
    recordGapCenter + 259682 = fullRecordGapValue05329 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05329_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05329 (fullRecordGapValue05329 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05329_not_prime : ¬(recordGapCenter + 259682).Prime := by
  rw [fullRecordGapTerm05329_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05329, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05329_fast_pow_mod_ne_one

def fullRecordGapValue05330 : Nat := fullRecordGapCenterValue + 259746

theorem fullRecordGapTerm05330_eq_value :
    recordGapCenter + 259746 = fullRecordGapValue05330 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05330_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05330 (fullRecordGapValue05330 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05330_not_prime : ¬(recordGapCenter + 259746).Prime := by
  rw [fullRecordGapTerm05330_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05330, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05330_fast_pow_mod_ne_one

def fullRecordGapValue05331 : Nat := fullRecordGapCenterValue + 259802

theorem fullRecordGapTerm05331_eq_value :
    recordGapCenter + 259802 = fullRecordGapValue05331 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05331_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05331 (fullRecordGapValue05331 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05331_not_prime : ¬(recordGapCenter + 259802).Prime := by
  rw [fullRecordGapTerm05331_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05331, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05331_fast_pow_mod_ne_one

def fullRecordGapValue05332 : Nat := fullRecordGapCenterValue + 259878

theorem fullRecordGapTerm05332_eq_value :
    recordGapCenter + 259878 = fullRecordGapValue05332 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05332_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05332 (fullRecordGapValue05332 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05332_not_prime : ¬(recordGapCenter + 259878).Prime := by
  rw [fullRecordGapTerm05332_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05332, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05332_fast_pow_mod_ne_one

def fullRecordGapValue05333 : Nat := fullRecordGapCenterValue + 260006

theorem fullRecordGapTerm05333_eq_value :
    recordGapCenter + 260006 = fullRecordGapValue05333 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05333_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05333 (fullRecordGapValue05333 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05333_not_prime : ¬(recordGapCenter + 260006).Prime := by
  rw [fullRecordGapTerm05333_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05333, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05333_fast_pow_mod_ne_one

def fullRecordGapValue05334 : Nat := fullRecordGapCenterValue + 260012

theorem fullRecordGapTerm05334_eq_value :
    recordGapCenter + 260012 = fullRecordGapValue05334 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05334_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05334 (fullRecordGapValue05334 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05334_not_prime : ¬(recordGapCenter + 260012).Prime := by
  rw [fullRecordGapTerm05334_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05334, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05334_fast_pow_mod_ne_one

def fullRecordGapValue05335 : Nat := fullRecordGapCenterValue + 260198

theorem fullRecordGapTerm05335_eq_value :
    recordGapCenter + 260198 = fullRecordGapValue05335 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05335_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05335 (fullRecordGapValue05335 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05335_not_prime : ¬(recordGapCenter + 260198).Prime := by
  rw [fullRecordGapTerm05335_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05335, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05335_fast_pow_mod_ne_one

def fullRecordGapValue05336 : Nat := fullRecordGapCenterValue + 260342

theorem fullRecordGapTerm05336_eq_value :
    recordGapCenter + 260342 = fullRecordGapValue05336 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05336_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05336 (fullRecordGapValue05336 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05336_not_prime : ¬(recordGapCenter + 260342).Prime := by
  rw [fullRecordGapTerm05336_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05336, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05336_fast_pow_mod_ne_one

def fullRecordGapValue05337 : Nat := fullRecordGapCenterValue + 260492

theorem fullRecordGapTerm05337_eq_value :
    recordGapCenter + 260492 = fullRecordGapValue05337 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05337_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05337 (fullRecordGapValue05337 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05337_not_prime : ¬(recordGapCenter + 260492).Prime := by
  rw [fullRecordGapTerm05337_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05337, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05337_fast_pow_mod_ne_one

def fullRecordGapValue05338 : Nat := fullRecordGapCenterValue + 260522

theorem fullRecordGapTerm05338_eq_value :
    recordGapCenter + 260522 = fullRecordGapValue05338 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05338_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05338 (fullRecordGapValue05338 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05338_not_prime : ¬(recordGapCenter + 260522).Prime := by
  rw [fullRecordGapTerm05338_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05338, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05338_fast_pow_mod_ne_one

def fullRecordGapValue05339 : Nat := fullRecordGapCenterValue + 260558

theorem fullRecordGapTerm05339_eq_value :
    recordGapCenter + 260558 = fullRecordGapValue05339 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05339_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05339 (fullRecordGapValue05339 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05339_not_prime : ¬(recordGapCenter + 260558).Prime := by
  rw [fullRecordGapTerm05339_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05339, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05339_fast_pow_mod_ne_one

def fullRecordGapValue05340 : Nat := fullRecordGapCenterValue + 260562

theorem fullRecordGapTerm05340_eq_value :
    recordGapCenter + 260562 = fullRecordGapValue05340 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05340_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05340 (fullRecordGapValue05340 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05340_not_prime : ¬(recordGapCenter + 260562).Prime := by
  rw [fullRecordGapTerm05340_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05340, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05340_fast_pow_mod_ne_one

def fullRecordGapValue05341 : Nat := fullRecordGapCenterValue + 260726

theorem fullRecordGapTerm05341_eq_value :
    recordGapCenter + 260726 = fullRecordGapValue05341 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05341_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05341 (fullRecordGapValue05341 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05341_not_prime : ¬(recordGapCenter + 260726).Prime := by
  rw [fullRecordGapTerm05341_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05341, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05341_fast_pow_mod_ne_one

def fullRecordGapValue05342 : Nat := fullRecordGapCenterValue + 260732

theorem fullRecordGapTerm05342_eq_value :
    recordGapCenter + 260732 = fullRecordGapValue05342 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05342_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05342 (fullRecordGapValue05342 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05342_not_prime : ¬(recordGapCenter + 260732).Prime := by
  rw [fullRecordGapTerm05342_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05342, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05342_fast_pow_mod_ne_one

def fullRecordGapValue05343 : Nat := fullRecordGapCenterValue + 260738

theorem fullRecordGapTerm05343_eq_value :
    recordGapCenter + 260738 = fullRecordGapValue05343 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05343_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05343 (fullRecordGapValue05343 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05343_not_prime : ¬(recordGapCenter + 260738).Prime := by
  rw [fullRecordGapTerm05343_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05343, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05343_fast_pow_mod_ne_one

def fullRecordGapValue05344 : Nat := fullRecordGapCenterValue + 260822

theorem fullRecordGapTerm05344_eq_value :
    recordGapCenter + 260822 = fullRecordGapValue05344 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05344_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05344 (fullRecordGapValue05344 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05344_not_prime : ¬(recordGapCenter + 260822).Prime := by
  rw [fullRecordGapTerm05344_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05344, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05344_fast_pow_mod_ne_one

def fullRecordGapValue05345 : Nat := fullRecordGapCenterValue + 260846

theorem fullRecordGapTerm05345_eq_value :
    recordGapCenter + 260846 = fullRecordGapValue05345 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05345_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05345 (fullRecordGapValue05345 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05345_not_prime : ¬(recordGapCenter + 260846).Prime := by
  rw [fullRecordGapTerm05345_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05345, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05345_fast_pow_mod_ne_one

def fullRecordGapValue05346 : Nat := fullRecordGapCenterValue + 260922

theorem fullRecordGapTerm05346_eq_value :
    recordGapCenter + 260922 = fullRecordGapValue05346 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05346_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05346 (fullRecordGapValue05346 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05346_not_prime : ¬(recordGapCenter + 260922).Prime := by
  rw [fullRecordGapTerm05346_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05346, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05346_fast_pow_mod_ne_one

def fullRecordGapValue05347 : Nat := fullRecordGapCenterValue + 260978

theorem fullRecordGapTerm05347_eq_value :
    recordGapCenter + 260978 = fullRecordGapValue05347 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05347_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05347 (fullRecordGapValue05347 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05347_not_prime : ¬(recordGapCenter + 260978).Prime := by
  rw [fullRecordGapTerm05347_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05347, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05347_fast_pow_mod_ne_one

def fullRecordGapValue05348 : Nat := fullRecordGapCenterValue + 261068

theorem fullRecordGapTerm05348_eq_value :
    recordGapCenter + 261068 = fullRecordGapValue05348 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05348_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05348 (fullRecordGapValue05348 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05348_not_prime : ¬(recordGapCenter + 261068).Prime := by
  rw [fullRecordGapTerm05348_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05348, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05348_fast_pow_mod_ne_one

def fullRecordGapValue05349 : Nat := fullRecordGapCenterValue + 261236

theorem fullRecordGapTerm05349_eq_value :
    recordGapCenter + 261236 = fullRecordGapValue05349 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05349_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05349 (fullRecordGapValue05349 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05349_not_prime : ¬(recordGapCenter + 261236).Prime := by
  rw [fullRecordGapTerm05349_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05349, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05349_fast_pow_mod_ne_one

def fullRecordGapValue05350 : Nat := fullRecordGapCenterValue + 261258

theorem fullRecordGapTerm05350_eq_value :
    recordGapCenter + 261258 = fullRecordGapValue05350 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05350_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05350 (fullRecordGapValue05350 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05350_not_prime : ¬(recordGapCenter + 261258).Prime := by
  rw [fullRecordGapTerm05350_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05350, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05350_fast_pow_mod_ne_one

def fullRecordGapValue05351 : Nat := fullRecordGapCenterValue + 261278

theorem fullRecordGapTerm05351_eq_value :
    recordGapCenter + 261278 = fullRecordGapValue05351 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05351_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05351 (fullRecordGapValue05351 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05351_not_prime : ¬(recordGapCenter + 261278).Prime := by
  rw [fullRecordGapTerm05351_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05351, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05351_fast_pow_mod_ne_one

def fullRecordGapValue05352 : Nat := fullRecordGapCenterValue + 261308

theorem fullRecordGapTerm05352_eq_value :
    recordGapCenter + 261308 = fullRecordGapValue05352 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05352_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05352 (fullRecordGapValue05352 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05352_not_prime : ¬(recordGapCenter + 261308).Prime := by
  rw [fullRecordGapTerm05352_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05352, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05352_fast_pow_mod_ne_one

def fullRecordGapValue05353 : Nat := fullRecordGapCenterValue + 261362

theorem fullRecordGapTerm05353_eq_value :
    recordGapCenter + 261362 = fullRecordGapValue05353 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05353_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05353 (fullRecordGapValue05353 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05353_not_prime : ¬(recordGapCenter + 261362).Prime := by
  rw [fullRecordGapTerm05353_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05353, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05353_fast_pow_mod_ne_one

def fullRecordGapValue05354 : Nat := fullRecordGapCenterValue + 261398

theorem fullRecordGapTerm05354_eq_value :
    recordGapCenter + 261398 = fullRecordGapValue05354 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05354_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05354 (fullRecordGapValue05354 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05354_not_prime : ¬(recordGapCenter + 261398).Prime := by
  rw [fullRecordGapTerm05354_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05354, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05354_fast_pow_mod_ne_one

def fullRecordGapValue05355 : Nat := fullRecordGapCenterValue + 261788

theorem fullRecordGapTerm05355_eq_value :
    recordGapCenter + 261788 = fullRecordGapValue05355 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05355_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05355 (fullRecordGapValue05355 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05355_not_prime : ¬(recordGapCenter + 261788).Prime := by
  rw [fullRecordGapTerm05355_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05355, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05355_fast_pow_mod_ne_one

def fullRecordGapValue05356 : Nat := fullRecordGapCenterValue + 261798

theorem fullRecordGapTerm05356_eq_value :
    recordGapCenter + 261798 = fullRecordGapValue05356 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05356_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05356 (fullRecordGapValue05356 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05356_not_prime : ¬(recordGapCenter + 261798).Prime := by
  rw [fullRecordGapTerm05356_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05356, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05356_fast_pow_mod_ne_one

def fullRecordGapValue05357 : Nat := fullRecordGapCenterValue + 261938

theorem fullRecordGapTerm05357_eq_value :
    recordGapCenter + 261938 = fullRecordGapValue05357 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05357_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05357 (fullRecordGapValue05357 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05357_not_prime : ¬(recordGapCenter + 261938).Prime := by
  rw [fullRecordGapTerm05357_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05357, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05357_fast_pow_mod_ne_one

def fullRecordGapValue05358 : Nat := fullRecordGapCenterValue + 261962

theorem fullRecordGapTerm05358_eq_value :
    recordGapCenter + 261962 = fullRecordGapValue05358 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05358_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05358 (fullRecordGapValue05358 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05358_not_prime : ¬(recordGapCenter + 261962).Prime := by
  rw [fullRecordGapTerm05358_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05358, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05358_fast_pow_mod_ne_one

def fullRecordGapValue05359 : Nat := fullRecordGapCenterValue + 262118

theorem fullRecordGapTerm05359_eq_value :
    recordGapCenter + 262118 = fullRecordGapValue05359 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05359_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05359 (fullRecordGapValue05359 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05359_not_prime : ¬(recordGapCenter + 262118).Prime := by
  rw [fullRecordGapTerm05359_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05359, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05359_fast_pow_mod_ne_one

def fullRecordGapValue05360 : Nat := fullRecordGapCenterValue + 262172

theorem fullRecordGapTerm05360_eq_value :
    recordGapCenter + 262172 = fullRecordGapValue05360 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05360_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05360 (fullRecordGapValue05360 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05360_not_prime : ¬(recordGapCenter + 262172).Prime := by
  rw [fullRecordGapTerm05360_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05360, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05360_fast_pow_mod_ne_one

def fullRecordGapValue05361 : Nat := fullRecordGapCenterValue + 262406

theorem fullRecordGapTerm05361_eq_value :
    recordGapCenter + 262406 = fullRecordGapValue05361 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05361_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05361 (fullRecordGapValue05361 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05361_not_prime : ¬(recordGapCenter + 262406).Prime := by
  rw [fullRecordGapTerm05361_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05361, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05361_fast_pow_mod_ne_one

def fullRecordGapValue05362 : Nat := fullRecordGapCenterValue + 262440

theorem fullRecordGapTerm05362_eq_value :
    recordGapCenter + 262440 = fullRecordGapValue05362 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05362_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05362 (fullRecordGapValue05362 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05362_not_prime : ¬(recordGapCenter + 262440).Prime := by
  rw [fullRecordGapTerm05362_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05362, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05362_fast_pow_mod_ne_one

def fullRecordGapValue05363 : Nat := fullRecordGapCenterValue + 262442

theorem fullRecordGapTerm05363_eq_value :
    recordGapCenter + 262442 = fullRecordGapValue05363 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05363_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05363 (fullRecordGapValue05363 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05363_not_prime : ¬(recordGapCenter + 262442).Prime := by
  rw [fullRecordGapTerm05363_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05363, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05363_fast_pow_mod_ne_one

def fullRecordGapValue05364 : Nat := fullRecordGapCenterValue + 262502

theorem fullRecordGapTerm05364_eq_value :
    recordGapCenter + 262502 = fullRecordGapValue05364 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05364_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05364 (fullRecordGapValue05364 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05364_not_prime : ¬(recordGapCenter + 262502).Prime := by
  rw [fullRecordGapTerm05364_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05364, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05364_fast_pow_mod_ne_one

def fullRecordGapValue05365 : Nat := fullRecordGapCenterValue + 262532

theorem fullRecordGapTerm05365_eq_value :
    recordGapCenter + 262532 = fullRecordGapValue05365 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05365_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05365 (fullRecordGapValue05365 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05365_not_prime : ¬(recordGapCenter + 262532).Prime := by
  rw [fullRecordGapTerm05365_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05365, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05365_fast_pow_mod_ne_one

def fullRecordGapValue05366 : Nat := fullRecordGapCenterValue + 262622

theorem fullRecordGapTerm05366_eq_value :
    recordGapCenter + 262622 = fullRecordGapValue05366 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05366_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05366 (fullRecordGapValue05366 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05366_not_prime : ¬(recordGapCenter + 262622).Prime := by
  rw [fullRecordGapTerm05366_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05366, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05366_fast_pow_mod_ne_one

def fullRecordGapValue05367 : Nat := fullRecordGapCenterValue + 262628

theorem fullRecordGapTerm05367_eq_value :
    recordGapCenter + 262628 = fullRecordGapValue05367 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05367_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05367 (fullRecordGapValue05367 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05367_not_prime : ¬(recordGapCenter + 262628).Prime := by
  rw [fullRecordGapTerm05367_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05367, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05367_fast_pow_mod_ne_one

def fullRecordGapValue05368 : Nat := fullRecordGapCenterValue + 262686

theorem fullRecordGapTerm05368_eq_value :
    recordGapCenter + 262686 = fullRecordGapValue05368 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05368_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05368 (fullRecordGapValue05368 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05368_not_prime : ¬(recordGapCenter + 262686).Prime := by
  rw [fullRecordGapTerm05368_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05368, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05368_fast_pow_mod_ne_one

def fullRecordGapValue05369 : Nat := fullRecordGapCenterValue + 262826

theorem fullRecordGapTerm05369_eq_value :
    recordGapCenter + 262826 = fullRecordGapValue05369 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05369_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05369 (fullRecordGapValue05369 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05369_not_prime : ¬(recordGapCenter + 262826).Prime := by
  rw [fullRecordGapTerm05369_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05369, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05369_fast_pow_mod_ne_one

def fullRecordGapValue05370 : Nat := fullRecordGapCenterValue + 262862

theorem fullRecordGapTerm05370_eq_value :
    recordGapCenter + 262862 = fullRecordGapValue05370 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05370_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05370 (fullRecordGapValue05370 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05370_not_prime : ¬(recordGapCenter + 262862).Prime := by
  rw [fullRecordGapTerm05370_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05370, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05370_fast_pow_mod_ne_one

def fullRecordGapValue05371 : Nat := fullRecordGapCenterValue + 262868

theorem fullRecordGapTerm05371_eq_value :
    recordGapCenter + 262868 = fullRecordGapValue05371 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05371_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05371 (fullRecordGapValue05371 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05371_not_prime : ¬(recordGapCenter + 262868).Prime := by
  rw [fullRecordGapTerm05371_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05371, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05371_fast_pow_mod_ne_one

def fullRecordGapValue05372 : Nat := fullRecordGapCenterValue + 262958

theorem fullRecordGapTerm05372_eq_value :
    recordGapCenter + 262958 = fullRecordGapValue05372 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05372_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05372 (fullRecordGapValue05372 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05372_not_prime : ¬(recordGapCenter + 262958).Prime := by
  rw [fullRecordGapTerm05372_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05372, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05372_fast_pow_mod_ne_one

def fullRecordGapValue05373 : Nat := fullRecordGapCenterValue + 263342

theorem fullRecordGapTerm05373_eq_value :
    recordGapCenter + 263342 = fullRecordGapValue05373 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05373_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05373 (fullRecordGapValue05373 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05373_not_prime : ¬(recordGapCenter + 263342).Prime := by
  rw [fullRecordGapTerm05373_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05373, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05373_fast_pow_mod_ne_one

def fullRecordGapValue05374 : Nat := fullRecordGapCenterValue + 263462

theorem fullRecordGapTerm05374_eq_value :
    recordGapCenter + 263462 = fullRecordGapValue05374 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05374_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05374 (fullRecordGapValue05374 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05374_not_prime : ¬(recordGapCenter + 263462).Prime := by
  rw [fullRecordGapTerm05374_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05374, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05374_fast_pow_mod_ne_one

def fullRecordGapValue05375 : Nat := fullRecordGapCenterValue + 263478

theorem fullRecordGapTerm05375_eq_value :
    recordGapCenter + 263478 = fullRecordGapValue05375 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05375_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05375 (fullRecordGapValue05375 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05375_not_prime : ¬(recordGapCenter + 263478).Prime := by
  rw [fullRecordGapTerm05375_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05375, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05375_fast_pow_mod_ne_one

def fullRecordGapValue05376 : Nat := fullRecordGapCenterValue + 263706

theorem fullRecordGapTerm05376_eq_value :
    recordGapCenter + 263706 = fullRecordGapValue05376 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral05376_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue05376 (fullRecordGapValue05376 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm05376_not_prime : ¬(recordGapCenter + 263706).Prime := by
  rw [fullRecordGapTerm05376_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue05376, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral05376_fast_pow_mod_ne_one

end PrimeFactorUnimodality
