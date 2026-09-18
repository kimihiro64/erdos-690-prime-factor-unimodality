import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue01025 : Nat := fullRecordGapCenterValue - 374434

theorem fullRecordGapTerm01025_eq_value :
    recordGapCenter - 374434 = fullRecordGapValue01025 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01025_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01025 (fullRecordGapValue01025 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01025_not_prime : ¬(recordGapCenter - 374434).Prime := by
  rw [fullRecordGapTerm01025_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01025, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01025_fast_pow_mod_ne_one

def fullRecordGapValue01026 : Nat := fullRecordGapCenterValue - 374278

theorem fullRecordGapTerm01026_eq_value :
    recordGapCenter - 374278 = fullRecordGapValue01026 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01026_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01026 (fullRecordGapValue01026 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01026_not_prime : ¬(recordGapCenter - 374278).Prime := by
  rw [fullRecordGapTerm01026_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01026, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01026_fast_pow_mod_ne_one

def fullRecordGapValue01027 : Nat := fullRecordGapCenterValue - 374254

theorem fullRecordGapTerm01027_eq_value :
    recordGapCenter - 374254 = fullRecordGapValue01027 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01027_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01027 (fullRecordGapValue01027 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01027_not_prime : ¬(recordGapCenter - 374254).Prime := by
  rw [fullRecordGapTerm01027_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01027, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01027_fast_pow_mod_ne_one

def fullRecordGapValue01028 : Nat := fullRecordGapCenterValue - 374182

theorem fullRecordGapTerm01028_eq_value :
    recordGapCenter - 374182 = fullRecordGapValue01028 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01028_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01028 (fullRecordGapValue01028 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01028_not_prime : ¬(recordGapCenter - 374182).Prime := by
  rw [fullRecordGapTerm01028_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01028, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01028_fast_pow_mod_ne_one

def fullRecordGapValue01029 : Nat := fullRecordGapCenterValue - 374098

theorem fullRecordGapTerm01029_eq_value :
    recordGapCenter - 374098 = fullRecordGapValue01029 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01029_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01029 (fullRecordGapValue01029 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01029_not_prime : ¬(recordGapCenter - 374098).Prime := by
  rw [fullRecordGapTerm01029_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01029, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01029_fast_pow_mod_ne_one

def fullRecordGapValue01030 : Nat := fullRecordGapCenterValue - 373972

theorem fullRecordGapTerm01030_eq_value :
    recordGapCenter - 373972 = fullRecordGapValue01030 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01030_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01030 (fullRecordGapValue01030 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01030_not_prime : ¬(recordGapCenter - 373972).Prime := by
  rw [fullRecordGapTerm01030_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01030, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01030_fast_pow_mod_ne_one

def fullRecordGapValue01031 : Nat := fullRecordGapCenterValue - 373852

theorem fullRecordGapTerm01031_eq_value :
    recordGapCenter - 373852 = fullRecordGapValue01031 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01031_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01031 (fullRecordGapValue01031 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01031_not_prime : ¬(recordGapCenter - 373852).Prime := by
  rw [fullRecordGapTerm01031_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01031, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01031_fast_pow_mod_ne_one

def fullRecordGapValue01032 : Nat := fullRecordGapCenterValue - 373818

theorem fullRecordGapTerm01032_eq_value :
    recordGapCenter - 373818 = fullRecordGapValue01032 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01032_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01032 (fullRecordGapValue01032 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01032_not_prime : ¬(recordGapCenter - 373818).Prime := by
  rw [fullRecordGapTerm01032_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01032, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01032_fast_pow_mod_ne_one

def fullRecordGapValue01033 : Nat := fullRecordGapCenterValue - 373782

theorem fullRecordGapTerm01033_eq_value :
    recordGapCenter - 373782 = fullRecordGapValue01033 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01033_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01033 (fullRecordGapValue01033 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01033_not_prime : ¬(recordGapCenter - 373782).Prime := by
  rw [fullRecordGapTerm01033_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01033, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01033_fast_pow_mod_ne_one

def fullRecordGapValue01034 : Nat := fullRecordGapCenterValue - 373624

theorem fullRecordGapTerm01034_eq_value :
    recordGapCenter - 373624 = fullRecordGapValue01034 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01034_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01034 (fullRecordGapValue01034 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01034_not_prime : ¬(recordGapCenter - 373624).Prime := by
  rw [fullRecordGapTerm01034_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01034, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01034_fast_pow_mod_ne_one

def fullRecordGapValue01035 : Nat := fullRecordGapCenterValue - 373522

theorem fullRecordGapTerm01035_eq_value :
    recordGapCenter - 373522 = fullRecordGapValue01035 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01035_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01035 (fullRecordGapValue01035 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01035_not_prime : ¬(recordGapCenter - 373522).Prime := by
  rw [fullRecordGapTerm01035_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01035, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01035_fast_pow_mod_ne_one

def fullRecordGapValue01036 : Nat := fullRecordGapCenterValue - 373398

theorem fullRecordGapTerm01036_eq_value :
    recordGapCenter - 373398 = fullRecordGapValue01036 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01036_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01036 (fullRecordGapValue01036 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01036_not_prime : ¬(recordGapCenter - 373398).Prime := by
  rw [fullRecordGapTerm01036_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01036, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01036_fast_pow_mod_ne_one

def fullRecordGapValue01037 : Nat := fullRecordGapCenterValue - 373294

theorem fullRecordGapTerm01037_eq_value :
    recordGapCenter - 373294 = fullRecordGapValue01037 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01037_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01037 (fullRecordGapValue01037 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01037_not_prime : ¬(recordGapCenter - 373294).Prime := by
  rw [fullRecordGapTerm01037_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01037, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01037_fast_pow_mod_ne_one

def fullRecordGapValue01038 : Nat := fullRecordGapCenterValue - 373162

theorem fullRecordGapTerm01038_eq_value :
    recordGapCenter - 373162 = fullRecordGapValue01038 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01038_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01038 (fullRecordGapValue01038 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01038_not_prime : ¬(recordGapCenter - 373162).Prime := by
  rw [fullRecordGapTerm01038_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01038, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01038_fast_pow_mod_ne_one

def fullRecordGapValue01039 : Nat := fullRecordGapCenterValue - 373134

theorem fullRecordGapTerm01039_eq_value :
    recordGapCenter - 373134 = fullRecordGapValue01039 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01039_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01039 (fullRecordGapValue01039 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01039_not_prime : ¬(recordGapCenter - 373134).Prime := by
  rw [fullRecordGapTerm01039_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01039, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01039_fast_pow_mod_ne_one

def fullRecordGapValue01040 : Nat := fullRecordGapCenterValue - 373012

theorem fullRecordGapTerm01040_eq_value :
    recordGapCenter - 373012 = fullRecordGapValue01040 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01040_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01040 (fullRecordGapValue01040 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01040_not_prime : ¬(recordGapCenter - 373012).Prime := by
  rw [fullRecordGapTerm01040_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01040, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01040_fast_pow_mod_ne_one

def fullRecordGapValue01041 : Nat := fullRecordGapCenterValue - 372958

theorem fullRecordGapTerm01041_eq_value :
    recordGapCenter - 372958 = fullRecordGapValue01041 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01041_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01041 (fullRecordGapValue01041 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01041_not_prime : ¬(recordGapCenter - 372958).Prime := by
  rw [fullRecordGapTerm01041_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01041, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01041_fast_pow_mod_ne_one

def fullRecordGapValue01042 : Nat := fullRecordGapCenterValue - 372874

theorem fullRecordGapTerm01042_eq_value :
    recordGapCenter - 372874 = fullRecordGapValue01042 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01042_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01042 (fullRecordGapValue01042 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01042_not_prime : ¬(recordGapCenter - 372874).Prime := by
  rw [fullRecordGapTerm01042_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01042, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01042_fast_pow_mod_ne_one

def fullRecordGapValue01043 : Nat := fullRecordGapCenterValue - 372858

theorem fullRecordGapTerm01043_eq_value :
    recordGapCenter - 372858 = fullRecordGapValue01043 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01043_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01043 (fullRecordGapValue01043 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01043_not_prime : ¬(recordGapCenter - 372858).Prime := by
  rw [fullRecordGapTerm01043_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01043, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01043_fast_pow_mod_ne_one

def fullRecordGapValue01044 : Nat := fullRecordGapCenterValue - 372754

theorem fullRecordGapTerm01044_eq_value :
    recordGapCenter - 372754 = fullRecordGapValue01044 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01044_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01044 (fullRecordGapValue01044 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01044_not_prime : ¬(recordGapCenter - 372754).Prime := by
  rw [fullRecordGapTerm01044_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01044, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01044_fast_pow_mod_ne_one

def fullRecordGapValue01045 : Nat := fullRecordGapCenterValue - 372748

theorem fullRecordGapTerm01045_eq_value :
    recordGapCenter - 372748 = fullRecordGapValue01045 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01045_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01045 (fullRecordGapValue01045 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01045_not_prime : ¬(recordGapCenter - 372748).Prime := by
  rw [fullRecordGapTerm01045_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01045, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01045_fast_pow_mod_ne_one

def fullRecordGapValue01046 : Nat := fullRecordGapCenterValue - 372634

theorem fullRecordGapTerm01046_eq_value :
    recordGapCenter - 372634 = fullRecordGapValue01046 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01046_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01046 (fullRecordGapValue01046 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01046_not_prime : ¬(recordGapCenter - 372634).Prime := by
  rw [fullRecordGapTerm01046_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01046, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01046_fast_pow_mod_ne_one

def fullRecordGapValue01047 : Nat := fullRecordGapCenterValue - 372622

theorem fullRecordGapTerm01047_eq_value :
    recordGapCenter - 372622 = fullRecordGapValue01047 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01047_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01047 (fullRecordGapValue01047 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01047_not_prime : ¬(recordGapCenter - 372622).Prime := by
  rw [fullRecordGapTerm01047_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01047, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01047_fast_pow_mod_ne_one

def fullRecordGapValue01048 : Nat := fullRecordGapCenterValue - 372594

theorem fullRecordGapTerm01048_eq_value :
    recordGapCenter - 372594 = fullRecordGapValue01048 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01048_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01048 (fullRecordGapValue01048 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01048_not_prime : ¬(recordGapCenter - 372594).Prime := by
  rw [fullRecordGapTerm01048_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01048, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01048_fast_pow_mod_ne_one

def fullRecordGapValue01049 : Nat := fullRecordGapCenterValue - 372454

theorem fullRecordGapTerm01049_eq_value :
    recordGapCenter - 372454 = fullRecordGapValue01049 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01049_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01049 (fullRecordGapValue01049 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01049_not_prime : ¬(recordGapCenter - 372454).Prime := by
  rw [fullRecordGapTerm01049_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01049, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01049_fast_pow_mod_ne_one

def fullRecordGapValue01050 : Nat := fullRecordGapCenterValue - 372342

theorem fullRecordGapTerm01050_eq_value :
    recordGapCenter - 372342 = fullRecordGapValue01050 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01050_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01050 (fullRecordGapValue01050 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01050_not_prime : ¬(recordGapCenter - 372342).Prime := by
  rw [fullRecordGapTerm01050_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01050, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01050_fast_pow_mod_ne_one

def fullRecordGapValue01051 : Nat := fullRecordGapCenterValue - 372322

theorem fullRecordGapTerm01051_eq_value :
    recordGapCenter - 372322 = fullRecordGapValue01051 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01051_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01051 (fullRecordGapValue01051 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01051_not_prime : ¬(recordGapCenter - 372322).Prime := by
  rw [fullRecordGapTerm01051_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01051, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01051_fast_pow_mod_ne_one

def fullRecordGapValue01052 : Nat := fullRecordGapCenterValue - 372238

theorem fullRecordGapTerm01052_eq_value :
    recordGapCenter - 372238 = fullRecordGapValue01052 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01052_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01052 (fullRecordGapValue01052 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01052_not_prime : ¬(recordGapCenter - 372238).Prime := by
  rw [fullRecordGapTerm01052_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01052, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01052_fast_pow_mod_ne_one

def fullRecordGapValue01053 : Nat := fullRecordGapCenterValue - 372234

theorem fullRecordGapTerm01053_eq_value :
    recordGapCenter - 372234 = fullRecordGapValue01053 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01053_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01053 (fullRecordGapValue01053 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01053_not_prime : ¬(recordGapCenter - 372234).Prime := by
  rw [fullRecordGapTerm01053_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01053, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01053_fast_pow_mod_ne_one

def fullRecordGapValue01054 : Nat := fullRecordGapCenterValue - 372102

theorem fullRecordGapTerm01054_eq_value :
    recordGapCenter - 372102 = fullRecordGapValue01054 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01054_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01054 (fullRecordGapValue01054 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01054_not_prime : ¬(recordGapCenter - 372102).Prime := by
  rw [fullRecordGapTerm01054_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01054, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01054_fast_pow_mod_ne_one

def fullRecordGapValue01055 : Nat := fullRecordGapCenterValue - 372018

theorem fullRecordGapTerm01055_eq_value :
    recordGapCenter - 372018 = fullRecordGapValue01055 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01055_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01055 (fullRecordGapValue01055 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01055_not_prime : ¬(recordGapCenter - 372018).Prime := by
  rw [fullRecordGapTerm01055_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01055, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01055_fast_pow_mod_ne_one

def fullRecordGapValue01056 : Nat := fullRecordGapCenterValue - 372004

theorem fullRecordGapTerm01056_eq_value :
    recordGapCenter - 372004 = fullRecordGapValue01056 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01056_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01056 (fullRecordGapValue01056 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01056_not_prime : ¬(recordGapCenter - 372004).Prime := by
  rw [fullRecordGapTerm01056_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01056, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01056_fast_pow_mod_ne_one

def fullRecordGapValue01057 : Nat := fullRecordGapCenterValue - 371922

theorem fullRecordGapTerm01057_eq_value :
    recordGapCenter - 371922 = fullRecordGapValue01057 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01057_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01057 (fullRecordGapValue01057 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01057_not_prime : ¬(recordGapCenter - 371922).Prime := by
  rw [fullRecordGapTerm01057_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01057, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01057_fast_pow_mod_ne_one

def fullRecordGapValue01058 : Nat := fullRecordGapCenterValue - 371662

theorem fullRecordGapTerm01058_eq_value :
    recordGapCenter - 371662 = fullRecordGapValue01058 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01058_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01058 (fullRecordGapValue01058 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01058_not_prime : ¬(recordGapCenter - 371662).Prime := by
  rw [fullRecordGapTerm01058_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01058, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01058_fast_pow_mod_ne_one

def fullRecordGapValue01059 : Nat := fullRecordGapCenterValue - 371608

theorem fullRecordGapTerm01059_eq_value :
    recordGapCenter - 371608 = fullRecordGapValue01059 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01059_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01059 (fullRecordGapValue01059 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01059_not_prime : ¬(recordGapCenter - 371608).Prime := by
  rw [fullRecordGapTerm01059_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01059, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01059_fast_pow_mod_ne_one

def fullRecordGapValue01060 : Nat := fullRecordGapCenterValue - 371578

theorem fullRecordGapTerm01060_eq_value :
    recordGapCenter - 371578 = fullRecordGapValue01060 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01060_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01060 (fullRecordGapValue01060 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01060_not_prime : ¬(recordGapCenter - 371578).Prime := by
  rw [fullRecordGapTerm01060_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01060, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01060_fast_pow_mod_ne_one

def fullRecordGapValue01061 : Nat := fullRecordGapCenterValue - 371494

theorem fullRecordGapTerm01061_eq_value :
    recordGapCenter - 371494 = fullRecordGapValue01061 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01061_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01061 (fullRecordGapValue01061 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01061_not_prime : ¬(recordGapCenter - 371494).Prime := by
  rw [fullRecordGapTerm01061_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01061, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01061_fast_pow_mod_ne_one

def fullRecordGapValue01062 : Nat := fullRecordGapCenterValue - 371250

theorem fullRecordGapTerm01062_eq_value :
    recordGapCenter - 371250 = fullRecordGapValue01062 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01062_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01062 (fullRecordGapValue01062 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01062_not_prime : ¬(recordGapCenter - 371250).Prime := by
  rw [fullRecordGapTerm01062_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01062, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01062_fast_pow_mod_ne_one

def fullRecordGapValue01063 : Nat := fullRecordGapCenterValue - 371242

theorem fullRecordGapTerm01063_eq_value :
    recordGapCenter - 371242 = fullRecordGapValue01063 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01063_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01063 (fullRecordGapValue01063 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01063_not_prime : ¬(recordGapCenter - 371242).Prime := by
  rw [fullRecordGapTerm01063_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01063, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01063_fast_pow_mod_ne_one

def fullRecordGapValue01064 : Nat := fullRecordGapCenterValue - 371062

theorem fullRecordGapTerm01064_eq_value :
    recordGapCenter - 371062 = fullRecordGapValue01064 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01064_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01064 (fullRecordGapValue01064 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01064_not_prime : ¬(recordGapCenter - 371062).Prime := by
  rw [fullRecordGapTerm01064_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01064, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01064_fast_pow_mod_ne_one

def fullRecordGapValue01065 : Nat := fullRecordGapCenterValue - 371058

theorem fullRecordGapTerm01065_eq_value :
    recordGapCenter - 371058 = fullRecordGapValue01065 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01065_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01065 (fullRecordGapValue01065 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01065_not_prime : ¬(recordGapCenter - 371058).Prime := by
  rw [fullRecordGapTerm01065_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01065, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01065_fast_pow_mod_ne_one

def fullRecordGapValue01066 : Nat := fullRecordGapCenterValue - 370914

theorem fullRecordGapTerm01066_eq_value :
    recordGapCenter - 370914 = fullRecordGapValue01066 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01066_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01066 (fullRecordGapValue01066 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01066_not_prime : ¬(recordGapCenter - 370914).Prime := by
  rw [fullRecordGapTerm01066_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01066, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01066_fast_pow_mod_ne_one

def fullRecordGapValue01067 : Nat := fullRecordGapCenterValue - 370654

theorem fullRecordGapTerm01067_eq_value :
    recordGapCenter - 370654 = fullRecordGapValue01067 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01067_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01067 (fullRecordGapValue01067 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01067_not_prime : ¬(recordGapCenter - 370654).Prime := by
  rw [fullRecordGapTerm01067_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01067, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01067_fast_pow_mod_ne_one

def fullRecordGapValue01068 : Nat := fullRecordGapCenterValue - 370618

theorem fullRecordGapTerm01068_eq_value :
    recordGapCenter - 370618 = fullRecordGapValue01068 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01068_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01068 (fullRecordGapValue01068 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01068_not_prime : ¬(recordGapCenter - 370618).Prime := by
  rw [fullRecordGapTerm01068_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01068, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01068_fast_pow_mod_ne_one

def fullRecordGapValue01069 : Nat := fullRecordGapCenterValue - 370564

theorem fullRecordGapTerm01069_eq_value :
    recordGapCenter - 370564 = fullRecordGapValue01069 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01069_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01069 (fullRecordGapValue01069 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01069_not_prime : ¬(recordGapCenter - 370564).Prime := by
  rw [fullRecordGapTerm01069_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01069, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01069_fast_pow_mod_ne_one

def fullRecordGapValue01070 : Nat := fullRecordGapCenterValue - 370542

theorem fullRecordGapTerm01070_eq_value :
    recordGapCenter - 370542 = fullRecordGapValue01070 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01070_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01070 (fullRecordGapValue01070 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01070_not_prime : ¬(recordGapCenter - 370542).Prime := by
  rw [fullRecordGapTerm01070_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01070, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01070_fast_pow_mod_ne_one

def fullRecordGapValue01071 : Nat := fullRecordGapCenterValue - 370534

theorem fullRecordGapTerm01071_eq_value :
    recordGapCenter - 370534 = fullRecordGapValue01071 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01071_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01071 (fullRecordGapValue01071 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01071_not_prime : ¬(recordGapCenter - 370534).Prime := by
  rw [fullRecordGapTerm01071_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01071, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01071_fast_pow_mod_ne_one

def fullRecordGapValue01072 : Nat := fullRecordGapCenterValue - 370492

theorem fullRecordGapTerm01072_eq_value :
    recordGapCenter - 370492 = fullRecordGapValue01072 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01072_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01072 (fullRecordGapValue01072 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01072_not_prime : ¬(recordGapCenter - 370492).Prime := by
  rw [fullRecordGapTerm01072_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01072, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01072_fast_pow_mod_ne_one

def fullRecordGapValue01073 : Nat := fullRecordGapCenterValue - 370354

theorem fullRecordGapTerm01073_eq_value :
    recordGapCenter - 370354 = fullRecordGapValue01073 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01073_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01073 (fullRecordGapValue01073 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01073_not_prime : ¬(recordGapCenter - 370354).Prime := by
  rw [fullRecordGapTerm01073_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01073, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01073_fast_pow_mod_ne_one

def fullRecordGapValue01074 : Nat := fullRecordGapCenterValue - 370218

theorem fullRecordGapTerm01074_eq_value :
    recordGapCenter - 370218 = fullRecordGapValue01074 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01074_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01074 (fullRecordGapValue01074 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01074_not_prime : ¬(recordGapCenter - 370218).Prime := by
  rw [fullRecordGapTerm01074_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01074, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01074_fast_pow_mod_ne_one

def fullRecordGapValue01075 : Nat := fullRecordGapCenterValue - 370114

theorem fullRecordGapTerm01075_eq_value :
    recordGapCenter - 370114 = fullRecordGapValue01075 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01075_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01075 (fullRecordGapValue01075 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01075_not_prime : ¬(recordGapCenter - 370114).Prime := by
  rw [fullRecordGapTerm01075_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01075, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01075_fast_pow_mod_ne_one

def fullRecordGapValue01076 : Nat := fullRecordGapCenterValue - 370102

theorem fullRecordGapTerm01076_eq_value :
    recordGapCenter - 370102 = fullRecordGapValue01076 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01076_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01076 (fullRecordGapValue01076 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01076_not_prime : ¬(recordGapCenter - 370102).Prime := by
  rw [fullRecordGapTerm01076_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01076, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01076_fast_pow_mod_ne_one

def fullRecordGapValue01077 : Nat := fullRecordGapCenterValue - 370054

theorem fullRecordGapTerm01077_eq_value :
    recordGapCenter - 370054 = fullRecordGapValue01077 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01077_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01077 (fullRecordGapValue01077 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01077_not_prime : ¬(recordGapCenter - 370054).Prime := by
  rw [fullRecordGapTerm01077_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01077, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01077_fast_pow_mod_ne_one

def fullRecordGapValue01078 : Nat := fullRecordGapCenterValue - 370012

theorem fullRecordGapTerm01078_eq_value :
    recordGapCenter - 370012 = fullRecordGapValue01078 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01078_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01078 (fullRecordGapValue01078 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01078_not_prime : ¬(recordGapCenter - 370012).Prime := by
  rw [fullRecordGapTerm01078_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01078, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01078_fast_pow_mod_ne_one

def fullRecordGapValue01079 : Nat := fullRecordGapCenterValue - 369994

theorem fullRecordGapTerm01079_eq_value :
    recordGapCenter - 369994 = fullRecordGapValue01079 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01079_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01079 (fullRecordGapValue01079 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01079_not_prime : ¬(recordGapCenter - 369994).Prime := by
  rw [fullRecordGapTerm01079_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01079, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01079_fast_pow_mod_ne_one

def fullRecordGapValue01080 : Nat := fullRecordGapCenterValue - 369654

theorem fullRecordGapTerm01080_eq_value :
    recordGapCenter - 369654 = fullRecordGapValue01080 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01080_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01080 (fullRecordGapValue01080 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01080_not_prime : ¬(recordGapCenter - 369654).Prime := by
  rw [fullRecordGapTerm01080_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01080, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01080_fast_pow_mod_ne_one

def fullRecordGapValue01081 : Nat := fullRecordGapCenterValue - 369618

theorem fullRecordGapTerm01081_eq_value :
    recordGapCenter - 369618 = fullRecordGapValue01081 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01081_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01081 (fullRecordGapValue01081 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01081_not_prime : ¬(recordGapCenter - 369618).Prime := by
  rw [fullRecordGapTerm01081_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01081, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01081_fast_pow_mod_ne_one

def fullRecordGapValue01082 : Nat := fullRecordGapCenterValue - 369600

theorem fullRecordGapTerm01082_eq_value :
    recordGapCenter - 369600 = fullRecordGapValue01082 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01082_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01082 (fullRecordGapValue01082 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01082_not_prime : ¬(recordGapCenter - 369600).Prime := by
  rw [fullRecordGapTerm01082_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01082, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01082_fast_pow_mod_ne_one

def fullRecordGapValue01083 : Nat := fullRecordGapCenterValue - 369532

theorem fullRecordGapTerm01083_eq_value :
    recordGapCenter - 369532 = fullRecordGapValue01083 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01083_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01083 (fullRecordGapValue01083 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01083_not_prime : ¬(recordGapCenter - 369532).Prime := by
  rw [fullRecordGapTerm01083_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01083, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01083_fast_pow_mod_ne_one

def fullRecordGapValue01084 : Nat := fullRecordGapCenterValue - 369508

theorem fullRecordGapTerm01084_eq_value :
    recordGapCenter - 369508 = fullRecordGapValue01084 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01084_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01084 (fullRecordGapValue01084 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01084_not_prime : ¬(recordGapCenter - 369508).Prime := by
  rw [fullRecordGapTerm01084_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01084, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01084_fast_pow_mod_ne_one

def fullRecordGapValue01085 : Nat := fullRecordGapCenterValue - 369498

theorem fullRecordGapTerm01085_eq_value :
    recordGapCenter - 369498 = fullRecordGapValue01085 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01085_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01085 (fullRecordGapValue01085 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01085_not_prime : ¬(recordGapCenter - 369498).Prime := by
  rw [fullRecordGapTerm01085_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01085, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01085_fast_pow_mod_ne_one

def fullRecordGapValue01086 : Nat := fullRecordGapCenterValue - 369388

theorem fullRecordGapTerm01086_eq_value :
    recordGapCenter - 369388 = fullRecordGapValue01086 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01086_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01086 (fullRecordGapValue01086 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01086_not_prime : ¬(recordGapCenter - 369388).Prime := by
  rw [fullRecordGapTerm01086_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01086, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01086_fast_pow_mod_ne_one

def fullRecordGapValue01087 : Nat := fullRecordGapCenterValue - 369268

theorem fullRecordGapTerm01087_eq_value :
    recordGapCenter - 369268 = fullRecordGapValue01087 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01087_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01087 (fullRecordGapValue01087 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01087_not_prime : ¬(recordGapCenter - 369268).Prime := by
  rw [fullRecordGapTerm01087_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01087, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01087_fast_pow_mod_ne_one

def fullRecordGapValue01088 : Nat := fullRecordGapCenterValue - 369214

theorem fullRecordGapTerm01088_eq_value :
    recordGapCenter - 369214 = fullRecordGapValue01088 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01088_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01088 (fullRecordGapValue01088 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01088_not_prime : ¬(recordGapCenter - 369214).Prime := by
  rw [fullRecordGapTerm01088_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01088, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01088_fast_pow_mod_ne_one

def fullRecordGapValue01089 : Nat := fullRecordGapCenterValue - 369154

theorem fullRecordGapTerm01089_eq_value :
    recordGapCenter - 369154 = fullRecordGapValue01089 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01089_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01089 (fullRecordGapValue01089 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01089_not_prime : ¬(recordGapCenter - 369154).Prime := by
  rw [fullRecordGapTerm01089_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01089, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01089_fast_pow_mod_ne_one

def fullRecordGapValue01090 : Nat := fullRecordGapCenterValue - 369114

theorem fullRecordGapTerm01090_eq_value :
    recordGapCenter - 369114 = fullRecordGapValue01090 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01090_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01090 (fullRecordGapValue01090 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01090_not_prime : ¬(recordGapCenter - 369114).Prime := by
  rw [fullRecordGapTerm01090_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01090, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01090_fast_pow_mod_ne_one

def fullRecordGapValue01091 : Nat := fullRecordGapCenterValue - 369022

theorem fullRecordGapTerm01091_eq_value :
    recordGapCenter - 369022 = fullRecordGapValue01091 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01091_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01091 (fullRecordGapValue01091 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01091_not_prime : ¬(recordGapCenter - 369022).Prime := by
  rw [fullRecordGapTerm01091_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01091, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01091_fast_pow_mod_ne_one

def fullRecordGapValue01092 : Nat := fullRecordGapCenterValue - 368974

theorem fullRecordGapTerm01092_eq_value :
    recordGapCenter - 368974 = fullRecordGapValue01092 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01092_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01092 (fullRecordGapValue01092 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01092_not_prime : ¬(recordGapCenter - 368974).Prime := by
  rw [fullRecordGapTerm01092_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01092, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01092_fast_pow_mod_ne_one

def fullRecordGapValue01093 : Nat := fullRecordGapCenterValue - 368818

theorem fullRecordGapTerm01093_eq_value :
    recordGapCenter - 368818 = fullRecordGapValue01093 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01093_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01093 (fullRecordGapValue01093 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01093_not_prime : ¬(recordGapCenter - 368818).Prime := by
  rw [fullRecordGapTerm01093_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01093, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01093_fast_pow_mod_ne_one

def fullRecordGapValue01094 : Nat := fullRecordGapCenterValue - 368778

theorem fullRecordGapTerm01094_eq_value :
    recordGapCenter - 368778 = fullRecordGapValue01094 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01094_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01094 (fullRecordGapValue01094 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01094_not_prime : ¬(recordGapCenter - 368778).Prime := by
  rw [fullRecordGapTerm01094_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01094, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01094_fast_pow_mod_ne_one

def fullRecordGapValue01095 : Nat := fullRecordGapCenterValue - 368692

theorem fullRecordGapTerm01095_eq_value :
    recordGapCenter - 368692 = fullRecordGapValue01095 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01095_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01095 (fullRecordGapValue01095 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01095_not_prime : ¬(recordGapCenter - 368692).Prime := by
  rw [fullRecordGapTerm01095_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01095, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01095_fast_pow_mod_ne_one

def fullRecordGapValue01096 : Nat := fullRecordGapCenterValue - 368674

theorem fullRecordGapTerm01096_eq_value :
    recordGapCenter - 368674 = fullRecordGapValue01096 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01096_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01096 (fullRecordGapValue01096 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01096_not_prime : ¬(recordGapCenter - 368674).Prime := by
  rw [fullRecordGapTerm01096_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01096, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01096_fast_pow_mod_ne_one

def fullRecordGapValue01097 : Nat := fullRecordGapCenterValue - 368584

theorem fullRecordGapTerm01097_eq_value :
    recordGapCenter - 368584 = fullRecordGapValue01097 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01097_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01097 (fullRecordGapValue01097 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01097_not_prime : ¬(recordGapCenter - 368584).Prime := by
  rw [fullRecordGapTerm01097_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01097, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01097_fast_pow_mod_ne_one

def fullRecordGapValue01098 : Nat := fullRecordGapCenterValue - 368518

theorem fullRecordGapTerm01098_eq_value :
    recordGapCenter - 368518 = fullRecordGapValue01098 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01098_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01098 (fullRecordGapValue01098 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01098_not_prime : ¬(recordGapCenter - 368518).Prime := by
  rw [fullRecordGapTerm01098_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01098, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01098_fast_pow_mod_ne_one

def fullRecordGapValue01099 : Nat := fullRecordGapCenterValue - 368422

theorem fullRecordGapTerm01099_eq_value :
    recordGapCenter - 368422 = fullRecordGapValue01099 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01099_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01099 (fullRecordGapValue01099 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01099_not_prime : ¬(recordGapCenter - 368422).Prime := by
  rw [fullRecordGapTerm01099_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01099, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01099_fast_pow_mod_ne_one

def fullRecordGapValue01100 : Nat := fullRecordGapCenterValue - 368398

theorem fullRecordGapTerm01100_eq_value :
    recordGapCenter - 368398 = fullRecordGapValue01100 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01100_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01100 (fullRecordGapValue01100 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01100_not_prime : ¬(recordGapCenter - 368398).Prime := by
  rw [fullRecordGapTerm01100_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01100, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01100_fast_pow_mod_ne_one

def fullRecordGapValue01101 : Nat := fullRecordGapCenterValue - 368374

theorem fullRecordGapTerm01101_eq_value :
    recordGapCenter - 368374 = fullRecordGapValue01101 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01101_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01101 (fullRecordGapValue01101 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01101_not_prime : ¬(recordGapCenter - 368374).Prime := by
  rw [fullRecordGapTerm01101_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01101, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01101_fast_pow_mod_ne_one

def fullRecordGapValue01102 : Nat := fullRecordGapCenterValue - 368332

theorem fullRecordGapTerm01102_eq_value :
    recordGapCenter - 368332 = fullRecordGapValue01102 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01102_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01102 (fullRecordGapValue01102 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01102_not_prime : ¬(recordGapCenter - 368332).Prime := by
  rw [fullRecordGapTerm01102_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01102, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01102_fast_pow_mod_ne_one

def fullRecordGapValue01103 : Nat := fullRecordGapCenterValue - 368314

theorem fullRecordGapTerm01103_eq_value :
    recordGapCenter - 368314 = fullRecordGapValue01103 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01103_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01103 (fullRecordGapValue01103 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01103_not_prime : ¬(recordGapCenter - 368314).Prime := by
  rw [fullRecordGapTerm01103_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01103, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01103_fast_pow_mod_ne_one

def fullRecordGapValue01104 : Nat := fullRecordGapCenterValue - 368308

theorem fullRecordGapTerm01104_eq_value :
    recordGapCenter - 368308 = fullRecordGapValue01104 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01104_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01104 (fullRecordGapValue01104 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01104_not_prime : ¬(recordGapCenter - 368308).Prime := by
  rw [fullRecordGapTerm01104_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01104, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01104_fast_pow_mod_ne_one

def fullRecordGapValue01105 : Nat := fullRecordGapCenterValue - 368164

theorem fullRecordGapTerm01105_eq_value :
    recordGapCenter - 368164 = fullRecordGapValue01105 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01105_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01105 (fullRecordGapValue01105 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01105_not_prime : ¬(recordGapCenter - 368164).Prime := by
  rw [fullRecordGapTerm01105_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01105, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01105_fast_pow_mod_ne_one

def fullRecordGapValue01106 : Nat := fullRecordGapCenterValue - 368062

theorem fullRecordGapTerm01106_eq_value :
    recordGapCenter - 368062 = fullRecordGapValue01106 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01106_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01106 (fullRecordGapValue01106 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01106_not_prime : ¬(recordGapCenter - 368062).Prime := by
  rw [fullRecordGapTerm01106_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01106, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01106_fast_pow_mod_ne_one

def fullRecordGapValue01107 : Nat := fullRecordGapCenterValue - 368058

theorem fullRecordGapTerm01107_eq_value :
    recordGapCenter - 368058 = fullRecordGapValue01107 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01107_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01107 (fullRecordGapValue01107 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01107_not_prime : ¬(recordGapCenter - 368058).Prime := by
  rw [fullRecordGapTerm01107_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01107, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01107_fast_pow_mod_ne_one

def fullRecordGapValue01108 : Nat := fullRecordGapCenterValue - 368034

theorem fullRecordGapTerm01108_eq_value :
    recordGapCenter - 368034 = fullRecordGapValue01108 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01108_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01108 (fullRecordGapValue01108 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01108_not_prime : ¬(recordGapCenter - 368034).Prime := by
  rw [fullRecordGapTerm01108_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01108, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01108_fast_pow_mod_ne_one

def fullRecordGapValue01109 : Nat := fullRecordGapCenterValue - 368014

theorem fullRecordGapTerm01109_eq_value :
    recordGapCenter - 368014 = fullRecordGapValue01109 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01109_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01109 (fullRecordGapValue01109 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01109_not_prime : ¬(recordGapCenter - 368014).Prime := by
  rw [fullRecordGapTerm01109_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01109, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01109_fast_pow_mod_ne_one

def fullRecordGapValue01110 : Nat := fullRecordGapCenterValue - 367918

theorem fullRecordGapTerm01110_eq_value :
    recordGapCenter - 367918 = fullRecordGapValue01110 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01110_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01110 (fullRecordGapValue01110 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01110_not_prime : ¬(recordGapCenter - 367918).Prime := by
  rw [fullRecordGapTerm01110_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01110, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01110_fast_pow_mod_ne_one

def fullRecordGapValue01111 : Nat := fullRecordGapCenterValue - 367912

theorem fullRecordGapTerm01111_eq_value :
    recordGapCenter - 367912 = fullRecordGapValue01111 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01111_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01111 (fullRecordGapValue01111 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01111_not_prime : ¬(recordGapCenter - 367912).Prime := by
  rw [fullRecordGapTerm01111_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01111, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01111_fast_pow_mod_ne_one

def fullRecordGapValue01112 : Nat := fullRecordGapCenterValue - 367762

theorem fullRecordGapTerm01112_eq_value :
    recordGapCenter - 367762 = fullRecordGapValue01112 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01112_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01112 (fullRecordGapValue01112 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01112_not_prime : ¬(recordGapCenter - 367762).Prime := by
  rw [fullRecordGapTerm01112_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01112, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01112_fast_pow_mod_ne_one

def fullRecordGapValue01113 : Nat := fullRecordGapCenterValue - 367672

theorem fullRecordGapTerm01113_eq_value :
    recordGapCenter - 367672 = fullRecordGapValue01113 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01113_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01113 (fullRecordGapValue01113 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01113_not_prime : ¬(recordGapCenter - 367672).Prime := by
  rw [fullRecordGapTerm01113_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01113, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01113_fast_pow_mod_ne_one

def fullRecordGapValue01114 : Nat := fullRecordGapCenterValue - 367594

theorem fullRecordGapTerm01114_eq_value :
    recordGapCenter - 367594 = fullRecordGapValue01114 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01114_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01114 (fullRecordGapValue01114 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01114_not_prime : ¬(recordGapCenter - 367594).Prime := by
  rw [fullRecordGapTerm01114_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01114, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01114_fast_pow_mod_ne_one

def fullRecordGapValue01115 : Nat := fullRecordGapCenterValue - 367204

theorem fullRecordGapTerm01115_eq_value :
    recordGapCenter - 367204 = fullRecordGapValue01115 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01115_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01115 (fullRecordGapValue01115 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01115_not_prime : ¬(recordGapCenter - 367204).Prime := by
  rw [fullRecordGapTerm01115_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01115, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01115_fast_pow_mod_ne_one

def fullRecordGapValue01116 : Nat := fullRecordGapCenterValue - 367084

theorem fullRecordGapTerm01116_eq_value :
    recordGapCenter - 367084 = fullRecordGapValue01116 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01116_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01116 (fullRecordGapValue01116 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01116_not_prime : ¬(recordGapCenter - 367084).Prime := by
  rw [fullRecordGapTerm01116_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01116, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01116_fast_pow_mod_ne_one

def fullRecordGapValue01117 : Nat := fullRecordGapCenterValue - 367012

theorem fullRecordGapTerm01117_eq_value :
    recordGapCenter - 367012 = fullRecordGapValue01117 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01117_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01117 (fullRecordGapValue01117 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01117_not_prime : ¬(recordGapCenter - 367012).Prime := by
  rw [fullRecordGapTerm01117_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01117, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01117_fast_pow_mod_ne_one

def fullRecordGapValue01118 : Nat := fullRecordGapCenterValue - 366994

theorem fullRecordGapTerm01118_eq_value :
    recordGapCenter - 366994 = fullRecordGapValue01118 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01118_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01118 (fullRecordGapValue01118 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01118_not_prime : ¬(recordGapCenter - 366994).Prime := by
  rw [fullRecordGapTerm01118_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01118, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01118_fast_pow_mod_ne_one

def fullRecordGapValue01119 : Nat := fullRecordGapCenterValue - 366922

theorem fullRecordGapTerm01119_eq_value :
    recordGapCenter - 366922 = fullRecordGapValue01119 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01119_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01119 (fullRecordGapValue01119 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01119_not_prime : ¬(recordGapCenter - 366922).Prime := by
  rw [fullRecordGapTerm01119_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01119, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01119_fast_pow_mod_ne_one

def fullRecordGapValue01120 : Nat := fullRecordGapCenterValue - 366844

theorem fullRecordGapTerm01120_eq_value :
    recordGapCenter - 366844 = fullRecordGapValue01120 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01120_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01120 (fullRecordGapValue01120 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01120_not_prime : ¬(recordGapCenter - 366844).Prime := by
  rw [fullRecordGapTerm01120_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01120, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01120_fast_pow_mod_ne_one

def fullRecordGapValue01121 : Nat := fullRecordGapCenterValue - 366774

theorem fullRecordGapTerm01121_eq_value :
    recordGapCenter - 366774 = fullRecordGapValue01121 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01121_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01121 (fullRecordGapValue01121 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01121_not_prime : ¬(recordGapCenter - 366774).Prime := by
  rw [fullRecordGapTerm01121_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01121, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01121_fast_pow_mod_ne_one

def fullRecordGapValue01122 : Nat := fullRecordGapCenterValue - 366594

theorem fullRecordGapTerm01122_eq_value :
    recordGapCenter - 366594 = fullRecordGapValue01122 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01122_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01122 (fullRecordGapValue01122 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01122_not_prime : ¬(recordGapCenter - 366594).Prime := by
  rw [fullRecordGapTerm01122_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01122, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01122_fast_pow_mod_ne_one

def fullRecordGapValue01123 : Nat := fullRecordGapCenterValue - 366382

theorem fullRecordGapTerm01123_eq_value :
    recordGapCenter - 366382 = fullRecordGapValue01123 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01123_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01123 (fullRecordGapValue01123 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01123_not_prime : ¬(recordGapCenter - 366382).Prime := by
  rw [fullRecordGapTerm01123_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01123, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01123_fast_pow_mod_ne_one

def fullRecordGapValue01124 : Nat := fullRecordGapCenterValue - 366342

theorem fullRecordGapTerm01124_eq_value :
    recordGapCenter - 366342 = fullRecordGapValue01124 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01124_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01124 (fullRecordGapValue01124 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01124_not_prime : ¬(recordGapCenter - 366342).Prime := by
  rw [fullRecordGapTerm01124_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01124, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01124_fast_pow_mod_ne_one

def fullRecordGapValue01125 : Nat := fullRecordGapCenterValue - 366232

theorem fullRecordGapTerm01125_eq_value :
    recordGapCenter - 366232 = fullRecordGapValue01125 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01125_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01125 (fullRecordGapValue01125 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01125_not_prime : ¬(recordGapCenter - 366232).Prime := by
  rw [fullRecordGapTerm01125_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01125, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01125_fast_pow_mod_ne_one

def fullRecordGapValue01126 : Nat := fullRecordGapCenterValue - 366162

theorem fullRecordGapTerm01126_eq_value :
    recordGapCenter - 366162 = fullRecordGapValue01126 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01126_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01126 (fullRecordGapValue01126 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01126_not_prime : ¬(recordGapCenter - 366162).Prime := by
  rw [fullRecordGapTerm01126_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01126, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01126_fast_pow_mod_ne_one

def fullRecordGapValue01127 : Nat := fullRecordGapCenterValue - 366082

theorem fullRecordGapTerm01127_eq_value :
    recordGapCenter - 366082 = fullRecordGapValue01127 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01127_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01127 (fullRecordGapValue01127 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01127_not_prime : ¬(recordGapCenter - 366082).Prime := by
  rw [fullRecordGapTerm01127_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01127, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01127_fast_pow_mod_ne_one

def fullRecordGapValue01128 : Nat := fullRecordGapCenterValue - 366042

theorem fullRecordGapTerm01128_eq_value :
    recordGapCenter - 366042 = fullRecordGapValue01128 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01128_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01128 (fullRecordGapValue01128 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01128_not_prime : ¬(recordGapCenter - 366042).Prime := by
  rw [fullRecordGapTerm01128_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01128, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01128_fast_pow_mod_ne_one

def fullRecordGapValue01129 : Nat := fullRecordGapCenterValue - 365998

theorem fullRecordGapTerm01129_eq_value :
    recordGapCenter - 365998 = fullRecordGapValue01129 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01129_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01129 (fullRecordGapValue01129 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01129_not_prime : ¬(recordGapCenter - 365998).Prime := by
  rw [fullRecordGapTerm01129_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01129, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01129_fast_pow_mod_ne_one

def fullRecordGapValue01130 : Nat := fullRecordGapCenterValue - 365962

theorem fullRecordGapTerm01130_eq_value :
    recordGapCenter - 365962 = fullRecordGapValue01130 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01130_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01130 (fullRecordGapValue01130 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01130_not_prime : ¬(recordGapCenter - 365962).Prime := by
  rw [fullRecordGapTerm01130_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01130, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01130_fast_pow_mod_ne_one

def fullRecordGapValue01131 : Nat := fullRecordGapCenterValue - 365572

theorem fullRecordGapTerm01131_eq_value :
    recordGapCenter - 365572 = fullRecordGapValue01131 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01131_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01131 (fullRecordGapValue01131 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01131_not_prime : ¬(recordGapCenter - 365572).Prime := by
  rw [fullRecordGapTerm01131_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01131, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01131_fast_pow_mod_ne_one

def fullRecordGapValue01132 : Nat := fullRecordGapCenterValue - 365538

theorem fullRecordGapTerm01132_eq_value :
    recordGapCenter - 365538 = fullRecordGapValue01132 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01132_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01132 (fullRecordGapValue01132 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01132_not_prime : ¬(recordGapCenter - 365538).Prime := by
  rw [fullRecordGapTerm01132_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01132, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01132_fast_pow_mod_ne_one

def fullRecordGapValue01133 : Nat := fullRecordGapCenterValue - 365502

theorem fullRecordGapTerm01133_eq_value :
    recordGapCenter - 365502 = fullRecordGapValue01133 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01133_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01133 (fullRecordGapValue01133 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01133_not_prime : ¬(recordGapCenter - 365502).Prime := by
  rw [fullRecordGapTerm01133_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01133, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01133_fast_pow_mod_ne_one

def fullRecordGapValue01134 : Nat := fullRecordGapCenterValue - 365374

theorem fullRecordGapTerm01134_eq_value :
    recordGapCenter - 365374 = fullRecordGapValue01134 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01134_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01134 (fullRecordGapValue01134 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01134_not_prime : ¬(recordGapCenter - 365374).Prime := by
  rw [fullRecordGapTerm01134_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01134, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01134_fast_pow_mod_ne_one

def fullRecordGapValue01135 : Nat := fullRecordGapCenterValue - 365322

theorem fullRecordGapTerm01135_eq_value :
    recordGapCenter - 365322 = fullRecordGapValue01135 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01135_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01135 (fullRecordGapValue01135 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01135_not_prime : ¬(recordGapCenter - 365322).Prime := by
  rw [fullRecordGapTerm01135_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01135, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01135_fast_pow_mod_ne_one

def fullRecordGapValue01136 : Nat := fullRecordGapCenterValue - 365278

theorem fullRecordGapTerm01136_eq_value :
    recordGapCenter - 365278 = fullRecordGapValue01136 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01136_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01136 (fullRecordGapValue01136 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01136_not_prime : ¬(recordGapCenter - 365278).Prime := by
  rw [fullRecordGapTerm01136_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01136, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01136_fast_pow_mod_ne_one

def fullRecordGapValue01137 : Nat := fullRecordGapCenterValue - 365214

theorem fullRecordGapTerm01137_eq_value :
    recordGapCenter - 365214 = fullRecordGapValue01137 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01137_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01137 (fullRecordGapValue01137 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01137_not_prime : ¬(recordGapCenter - 365214).Prime := by
  rw [fullRecordGapTerm01137_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01137, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01137_fast_pow_mod_ne_one

def fullRecordGapValue01138 : Nat := fullRecordGapCenterValue - 365188

theorem fullRecordGapTerm01138_eq_value :
    recordGapCenter - 365188 = fullRecordGapValue01138 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01138_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01138 (fullRecordGapValue01138 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01138_not_prime : ¬(recordGapCenter - 365188).Prime := by
  rw [fullRecordGapTerm01138_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01138, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01138_fast_pow_mod_ne_one

def fullRecordGapValue01139 : Nat := fullRecordGapCenterValue - 365098

theorem fullRecordGapTerm01139_eq_value :
    recordGapCenter - 365098 = fullRecordGapValue01139 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01139_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01139 (fullRecordGapValue01139 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01139_not_prime : ¬(recordGapCenter - 365098).Prime := by
  rw [fullRecordGapTerm01139_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01139, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01139_fast_pow_mod_ne_one

def fullRecordGapValue01140 : Nat := fullRecordGapCenterValue - 364972

theorem fullRecordGapTerm01140_eq_value :
    recordGapCenter - 364972 = fullRecordGapValue01140 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01140_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01140 (fullRecordGapValue01140 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01140_not_prime : ¬(recordGapCenter - 364972).Prime := by
  rw [fullRecordGapTerm01140_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01140, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01140_fast_pow_mod_ne_one

def fullRecordGapValue01141 : Nat := fullRecordGapCenterValue - 364948

theorem fullRecordGapTerm01141_eq_value :
    recordGapCenter - 364948 = fullRecordGapValue01141 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01141_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01141 (fullRecordGapValue01141 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01141_not_prime : ¬(recordGapCenter - 364948).Prime := by
  rw [fullRecordGapTerm01141_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01141, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01141_fast_pow_mod_ne_one

def fullRecordGapValue01142 : Nat := fullRecordGapCenterValue - 364674

theorem fullRecordGapTerm01142_eq_value :
    recordGapCenter - 364674 = fullRecordGapValue01142 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01142_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01142 (fullRecordGapValue01142 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01142_not_prime : ¬(recordGapCenter - 364674).Prime := by
  rw [fullRecordGapTerm01142_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01142, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01142_fast_pow_mod_ne_one

def fullRecordGapValue01143 : Nat := fullRecordGapCenterValue - 364618

theorem fullRecordGapTerm01143_eq_value :
    recordGapCenter - 364618 = fullRecordGapValue01143 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01143_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01143 (fullRecordGapValue01143 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01143_not_prime : ¬(recordGapCenter - 364618).Prime := by
  rw [fullRecordGapTerm01143_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01143, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01143_fast_pow_mod_ne_one

def fullRecordGapValue01144 : Nat := fullRecordGapCenterValue - 364552

theorem fullRecordGapTerm01144_eq_value :
    recordGapCenter - 364552 = fullRecordGapValue01144 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01144_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01144 (fullRecordGapValue01144 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01144_not_prime : ¬(recordGapCenter - 364552).Prime := by
  rw [fullRecordGapTerm01144_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01144, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01144_fast_pow_mod_ne_one

def fullRecordGapValue01145 : Nat := fullRecordGapCenterValue - 364542

theorem fullRecordGapTerm01145_eq_value :
    recordGapCenter - 364542 = fullRecordGapValue01145 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01145_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01145 (fullRecordGapValue01145 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01145_not_prime : ¬(recordGapCenter - 364542).Prime := by
  rw [fullRecordGapTerm01145_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01145, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01145_fast_pow_mod_ne_one

def fullRecordGapValue01146 : Nat := fullRecordGapCenterValue - 364422

theorem fullRecordGapTerm01146_eq_value :
    recordGapCenter - 364422 = fullRecordGapValue01146 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01146_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01146 (fullRecordGapValue01146 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01146_not_prime : ¬(recordGapCenter - 364422).Prime := by
  rw [fullRecordGapTerm01146_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01146, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01146_fast_pow_mod_ne_one

def fullRecordGapValue01147 : Nat := fullRecordGapCenterValue - 364222

theorem fullRecordGapTerm01147_eq_value :
    recordGapCenter - 364222 = fullRecordGapValue01147 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01147_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01147 (fullRecordGapValue01147 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01147_not_prime : ¬(recordGapCenter - 364222).Prime := by
  rw [fullRecordGapTerm01147_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01147, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01147_fast_pow_mod_ne_one

def fullRecordGapValue01148 : Nat := fullRecordGapCenterValue - 364198

theorem fullRecordGapTerm01148_eq_value :
    recordGapCenter - 364198 = fullRecordGapValue01148 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01148_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01148 (fullRecordGapValue01148 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01148_not_prime : ¬(recordGapCenter - 364198).Prime := by
  rw [fullRecordGapTerm01148_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01148, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01148_fast_pow_mod_ne_one

def fullRecordGapValue01149 : Nat := fullRecordGapCenterValue - 364054

theorem fullRecordGapTerm01149_eq_value :
    recordGapCenter - 364054 = fullRecordGapValue01149 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01149_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01149 (fullRecordGapValue01149 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01149_not_prime : ¬(recordGapCenter - 364054).Prime := by
  rw [fullRecordGapTerm01149_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01149, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01149_fast_pow_mod_ne_one

def fullRecordGapValue01150 : Nat := fullRecordGapCenterValue - 364024

theorem fullRecordGapTerm01150_eq_value :
    recordGapCenter - 364024 = fullRecordGapValue01150 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01150_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01150 (fullRecordGapValue01150 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01150_not_prime : ¬(recordGapCenter - 364024).Prime := by
  rw [fullRecordGapTerm01150_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01150, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01150_fast_pow_mod_ne_one

def fullRecordGapValue01151 : Nat := fullRecordGapCenterValue - 363954

theorem fullRecordGapTerm01151_eq_value :
    recordGapCenter - 363954 = fullRecordGapValue01151 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01151_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01151 (fullRecordGapValue01151 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01151_not_prime : ¬(recordGapCenter - 363954).Prime := by
  rw [fullRecordGapTerm01151_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01151, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01151_fast_pow_mod_ne_one

def fullRecordGapValue01152 : Nat := fullRecordGapCenterValue - 363934

theorem fullRecordGapTerm01152_eq_value :
    recordGapCenter - 363934 = fullRecordGapValue01152 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01152_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01152 (fullRecordGapValue01152 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01152_not_prime : ¬(recordGapCenter - 363934).Prime := by
  rw [fullRecordGapTerm01152_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01152, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01152_fast_pow_mod_ne_one

def fullRecordGapValue01153 : Nat := fullRecordGapCenterValue - 363894

theorem fullRecordGapTerm01153_eq_value :
    recordGapCenter - 363894 = fullRecordGapValue01153 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01153_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01153 (fullRecordGapValue01153 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01153_not_prime : ¬(recordGapCenter - 363894).Prime := by
  rw [fullRecordGapTerm01153_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01153, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01153_fast_pow_mod_ne_one

def fullRecordGapValue01154 : Nat := fullRecordGapCenterValue - 363838

theorem fullRecordGapTerm01154_eq_value :
    recordGapCenter - 363838 = fullRecordGapValue01154 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01154_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01154 (fullRecordGapValue01154 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01154_not_prime : ¬(recordGapCenter - 363838).Prime := by
  rw [fullRecordGapTerm01154_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01154, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01154_fast_pow_mod_ne_one

def fullRecordGapValue01155 : Nat := fullRecordGapCenterValue - 363778

theorem fullRecordGapTerm01155_eq_value :
    recordGapCenter - 363778 = fullRecordGapValue01155 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01155_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01155 (fullRecordGapValue01155 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01155_not_prime : ¬(recordGapCenter - 363778).Prime := by
  rw [fullRecordGapTerm01155_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01155, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01155_fast_pow_mod_ne_one

def fullRecordGapValue01156 : Nat := fullRecordGapCenterValue - 363604

theorem fullRecordGapTerm01156_eq_value :
    recordGapCenter - 363604 = fullRecordGapValue01156 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01156_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01156 (fullRecordGapValue01156 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01156_not_prime : ¬(recordGapCenter - 363604).Prime := by
  rw [fullRecordGapTerm01156_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01156, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01156_fast_pow_mod_ne_one

def fullRecordGapValue01157 : Nat := fullRecordGapCenterValue - 363502

theorem fullRecordGapTerm01157_eq_value :
    recordGapCenter - 363502 = fullRecordGapValue01157 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01157_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01157 (fullRecordGapValue01157 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01157_not_prime : ¬(recordGapCenter - 363502).Prime := by
  rw [fullRecordGapTerm01157_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01157, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01157_fast_pow_mod_ne_one

def fullRecordGapValue01158 : Nat := fullRecordGapCenterValue - 363388

theorem fullRecordGapTerm01158_eq_value :
    recordGapCenter - 363388 = fullRecordGapValue01158 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01158_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01158 (fullRecordGapValue01158 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01158_not_prime : ¬(recordGapCenter - 363388).Prime := by
  rw [fullRecordGapTerm01158_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01158, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01158_fast_pow_mod_ne_one

def fullRecordGapValue01159 : Nat := fullRecordGapCenterValue - 363304

theorem fullRecordGapTerm01159_eq_value :
    recordGapCenter - 363304 = fullRecordGapValue01159 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01159_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01159 (fullRecordGapValue01159 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01159_not_prime : ¬(recordGapCenter - 363304).Prime := by
  rw [fullRecordGapTerm01159_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01159, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01159_fast_pow_mod_ne_one

def fullRecordGapValue01160 : Nat := fullRecordGapCenterValue - 363172

theorem fullRecordGapTerm01160_eq_value :
    recordGapCenter - 363172 = fullRecordGapValue01160 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01160_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01160 (fullRecordGapValue01160 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01160_not_prime : ¬(recordGapCenter - 363172).Prime := by
  rw [fullRecordGapTerm01160_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01160, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01160_fast_pow_mod_ne_one

def fullRecordGapValue01161 : Nat := fullRecordGapCenterValue - 363162

theorem fullRecordGapTerm01161_eq_value :
    recordGapCenter - 363162 = fullRecordGapValue01161 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01161_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01161 (fullRecordGapValue01161 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01161_not_prime : ¬(recordGapCenter - 363162).Prime := by
  rw [fullRecordGapTerm01161_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01161, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01161_fast_pow_mod_ne_one

def fullRecordGapValue01162 : Nat := fullRecordGapCenterValue - 362998

theorem fullRecordGapTerm01162_eq_value :
    recordGapCenter - 362998 = fullRecordGapValue01162 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01162_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01162 (fullRecordGapValue01162 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01162_not_prime : ¬(recordGapCenter - 362998).Prime := by
  rw [fullRecordGapTerm01162_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01162, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01162_fast_pow_mod_ne_one

def fullRecordGapValue01163 : Nat := fullRecordGapCenterValue - 362794

theorem fullRecordGapTerm01163_eq_value :
    recordGapCenter - 362794 = fullRecordGapValue01163 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01163_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01163 (fullRecordGapValue01163 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01163_not_prime : ¬(recordGapCenter - 362794).Prime := by
  rw [fullRecordGapTerm01163_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01163, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01163_fast_pow_mod_ne_one

def fullRecordGapValue01164 : Nat := fullRecordGapCenterValue - 362728

theorem fullRecordGapTerm01164_eq_value :
    recordGapCenter - 362728 = fullRecordGapValue01164 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01164_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01164 (fullRecordGapValue01164 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01164_not_prime : ¬(recordGapCenter - 362728).Prime := by
  rw [fullRecordGapTerm01164_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01164, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01164_fast_pow_mod_ne_one

def fullRecordGapValue01165 : Nat := fullRecordGapCenterValue - 362694

theorem fullRecordGapTerm01165_eq_value :
    recordGapCenter - 362694 = fullRecordGapValue01165 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01165_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01165 (fullRecordGapValue01165 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01165_not_prime : ¬(recordGapCenter - 362694).Prime := by
  rw [fullRecordGapTerm01165_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01165, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01165_fast_pow_mod_ne_one

def fullRecordGapValue01166 : Nat := fullRecordGapCenterValue - 362632

theorem fullRecordGapTerm01166_eq_value :
    recordGapCenter - 362632 = fullRecordGapValue01166 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01166_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01166 (fullRecordGapValue01166 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01166_not_prime : ¬(recordGapCenter - 362632).Prime := by
  rw [fullRecordGapTerm01166_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01166, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01166_fast_pow_mod_ne_one

def fullRecordGapValue01167 : Nat := fullRecordGapCenterValue - 362602

theorem fullRecordGapTerm01167_eq_value :
    recordGapCenter - 362602 = fullRecordGapValue01167 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01167_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01167 (fullRecordGapValue01167 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01167_not_prime : ¬(recordGapCenter - 362602).Prime := by
  rw [fullRecordGapTerm01167_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01167, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01167_fast_pow_mod_ne_one

def fullRecordGapValue01168 : Nat := fullRecordGapCenterValue - 362562

theorem fullRecordGapTerm01168_eq_value :
    recordGapCenter - 362562 = fullRecordGapValue01168 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01168_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01168 (fullRecordGapValue01168 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01168_not_prime : ¬(recordGapCenter - 362562).Prime := by
  rw [fullRecordGapTerm01168_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01168, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01168_fast_pow_mod_ne_one

def fullRecordGapValue01169 : Nat := fullRecordGapCenterValue - 362554

theorem fullRecordGapTerm01169_eq_value :
    recordGapCenter - 362554 = fullRecordGapValue01169 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01169_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01169 (fullRecordGapValue01169 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01169_not_prime : ¬(recordGapCenter - 362554).Prime := by
  rw [fullRecordGapTerm01169_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01169, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01169_fast_pow_mod_ne_one

def fullRecordGapValue01170 : Nat := fullRecordGapCenterValue - 362478

theorem fullRecordGapTerm01170_eq_value :
    recordGapCenter - 362478 = fullRecordGapValue01170 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01170_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01170 (fullRecordGapValue01170 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01170_not_prime : ¬(recordGapCenter - 362478).Prime := by
  rw [fullRecordGapTerm01170_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01170, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01170_fast_pow_mod_ne_one

def fullRecordGapValue01171 : Nat := fullRecordGapCenterValue - 362422

theorem fullRecordGapTerm01171_eq_value :
    recordGapCenter - 362422 = fullRecordGapValue01171 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01171_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01171 (fullRecordGapValue01171 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01171_not_prime : ¬(recordGapCenter - 362422).Prime := by
  rw [fullRecordGapTerm01171_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01171, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01171_fast_pow_mod_ne_one

def fullRecordGapValue01172 : Nat := fullRecordGapCenterValue - 362382

theorem fullRecordGapTerm01172_eq_value :
    recordGapCenter - 362382 = fullRecordGapValue01172 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01172_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01172 (fullRecordGapValue01172 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01172_not_prime : ¬(recordGapCenter - 362382).Prime := by
  rw [fullRecordGapTerm01172_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01172, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01172_fast_pow_mod_ne_one

def fullRecordGapValue01173 : Nat := fullRecordGapCenterValue - 362248

theorem fullRecordGapTerm01173_eq_value :
    recordGapCenter - 362248 = fullRecordGapValue01173 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01173_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01173 (fullRecordGapValue01173 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01173_not_prime : ¬(recordGapCenter - 362248).Prime := by
  rw [fullRecordGapTerm01173_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01173, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01173_fast_pow_mod_ne_one

def fullRecordGapValue01174 : Nat := fullRecordGapCenterValue - 362238

theorem fullRecordGapTerm01174_eq_value :
    recordGapCenter - 362238 = fullRecordGapValue01174 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01174_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01174 (fullRecordGapValue01174 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01174_not_prime : ¬(recordGapCenter - 362238).Prime := by
  rw [fullRecordGapTerm01174_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01174, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01174_fast_pow_mod_ne_one

def fullRecordGapValue01175 : Nat := fullRecordGapCenterValue - 362022

theorem fullRecordGapTerm01175_eq_value :
    recordGapCenter - 362022 = fullRecordGapValue01175 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01175_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01175 (fullRecordGapValue01175 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01175_not_prime : ¬(recordGapCenter - 362022).Prime := by
  rw [fullRecordGapTerm01175_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01175, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01175_fast_pow_mod_ne_one

def fullRecordGapValue01176 : Nat := fullRecordGapCenterValue - 361918

theorem fullRecordGapTerm01176_eq_value :
    recordGapCenter - 361918 = fullRecordGapValue01176 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01176_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01176 (fullRecordGapValue01176 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01176_not_prime : ¬(recordGapCenter - 361918).Prime := by
  rw [fullRecordGapTerm01176_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01176, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01176_fast_pow_mod_ne_one

def fullRecordGapValue01177 : Nat := fullRecordGapCenterValue - 361902

theorem fullRecordGapTerm01177_eq_value :
    recordGapCenter - 361902 = fullRecordGapValue01177 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01177_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01177 (fullRecordGapValue01177 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01177_not_prime : ¬(recordGapCenter - 361902).Prime := by
  rw [fullRecordGapTerm01177_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01177, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01177_fast_pow_mod_ne_one

def fullRecordGapValue01178 : Nat := fullRecordGapCenterValue - 361554

theorem fullRecordGapTerm01178_eq_value :
    recordGapCenter - 361554 = fullRecordGapValue01178 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01178_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01178 (fullRecordGapValue01178 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01178_not_prime : ¬(recordGapCenter - 361554).Prime := by
  rw [fullRecordGapTerm01178_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01178, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01178_fast_pow_mod_ne_one

def fullRecordGapValue01179 : Nat := fullRecordGapCenterValue - 361542

theorem fullRecordGapTerm01179_eq_value :
    recordGapCenter - 361542 = fullRecordGapValue01179 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01179_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01179 (fullRecordGapValue01179 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01179_not_prime : ¬(recordGapCenter - 361542).Prime := by
  rw [fullRecordGapTerm01179_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01179, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01179_fast_pow_mod_ne_one

def fullRecordGapValue01180 : Nat := fullRecordGapCenterValue - 361462

theorem fullRecordGapTerm01180_eq_value :
    recordGapCenter - 361462 = fullRecordGapValue01180 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01180_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01180 (fullRecordGapValue01180 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01180_not_prime : ¬(recordGapCenter - 361462).Prime := by
  rw [fullRecordGapTerm01180_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01180, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01180_fast_pow_mod_ne_one

def fullRecordGapValue01181 : Nat := fullRecordGapCenterValue - 361302

theorem fullRecordGapTerm01181_eq_value :
    recordGapCenter - 361302 = fullRecordGapValue01181 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01181_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01181 (fullRecordGapValue01181 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01181_not_prime : ¬(recordGapCenter - 361302).Prime := by
  rw [fullRecordGapTerm01181_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01181, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01181_fast_pow_mod_ne_one

def fullRecordGapValue01182 : Nat := fullRecordGapCenterValue - 361234

theorem fullRecordGapTerm01182_eq_value :
    recordGapCenter - 361234 = fullRecordGapValue01182 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01182_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01182 (fullRecordGapValue01182 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01182_not_prime : ¬(recordGapCenter - 361234).Prime := by
  rw [fullRecordGapTerm01182_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01182, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01182_fast_pow_mod_ne_one

def fullRecordGapValue01183 : Nat := fullRecordGapCenterValue - 361084

theorem fullRecordGapTerm01183_eq_value :
    recordGapCenter - 361084 = fullRecordGapValue01183 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01183_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01183 (fullRecordGapValue01183 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01183_not_prime : ¬(recordGapCenter - 361084).Prime := by
  rw [fullRecordGapTerm01183_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01183, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01183_fast_pow_mod_ne_one

def fullRecordGapValue01184 : Nat := fullRecordGapCenterValue - 360988

theorem fullRecordGapTerm01184_eq_value :
    recordGapCenter - 360988 = fullRecordGapValue01184 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01184_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01184 (fullRecordGapValue01184 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01184_not_prime : ¬(recordGapCenter - 360988).Prime := by
  rw [fullRecordGapTerm01184_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01184, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01184_fast_pow_mod_ne_one

def fullRecordGapValue01185 : Nat := fullRecordGapCenterValue - 360762

theorem fullRecordGapTerm01185_eq_value :
    recordGapCenter - 360762 = fullRecordGapValue01185 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01185_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01185 (fullRecordGapValue01185 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01185_not_prime : ¬(recordGapCenter - 360762).Prime := by
  rw [fullRecordGapTerm01185_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01185, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01185_fast_pow_mod_ne_one

def fullRecordGapValue01186 : Nat := fullRecordGapCenterValue - 360748

theorem fullRecordGapTerm01186_eq_value :
    recordGapCenter - 360748 = fullRecordGapValue01186 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01186_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01186 (fullRecordGapValue01186 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01186_not_prime : ¬(recordGapCenter - 360748).Prime := by
  rw [fullRecordGapTerm01186_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01186, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01186_fast_pow_mod_ne_one

def fullRecordGapValue01187 : Nat := fullRecordGapCenterValue - 360652

theorem fullRecordGapTerm01187_eq_value :
    recordGapCenter - 360652 = fullRecordGapValue01187 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01187_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01187 (fullRecordGapValue01187 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01187_not_prime : ¬(recordGapCenter - 360652).Prime := by
  rw [fullRecordGapTerm01187_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01187, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01187_fast_pow_mod_ne_one

def fullRecordGapValue01188 : Nat := fullRecordGapCenterValue - 360642

theorem fullRecordGapTerm01188_eq_value :
    recordGapCenter - 360642 = fullRecordGapValue01188 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01188_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01188 (fullRecordGapValue01188 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01188_not_prime : ¬(recordGapCenter - 360642).Prime := by
  rw [fullRecordGapTerm01188_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01188, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01188_fast_pow_mod_ne_one

def fullRecordGapValue01189 : Nat := fullRecordGapCenterValue - 360534

theorem fullRecordGapTerm01189_eq_value :
    recordGapCenter - 360534 = fullRecordGapValue01189 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01189_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01189 (fullRecordGapValue01189 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01189_not_prime : ¬(recordGapCenter - 360534).Prime := by
  rw [fullRecordGapTerm01189_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01189, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01189_fast_pow_mod_ne_one

def fullRecordGapValue01190 : Nat := fullRecordGapCenterValue - 360448

theorem fullRecordGapTerm01190_eq_value :
    recordGapCenter - 360448 = fullRecordGapValue01190 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01190_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01190 (fullRecordGapValue01190 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01190_not_prime : ¬(recordGapCenter - 360448).Prime := by
  rw [fullRecordGapTerm01190_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01190, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01190_fast_pow_mod_ne_one

def fullRecordGapValue01191 : Nat := fullRecordGapCenterValue - 360442

theorem fullRecordGapTerm01191_eq_value :
    recordGapCenter - 360442 = fullRecordGapValue01191 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01191_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01191 (fullRecordGapValue01191 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01191_not_prime : ¬(recordGapCenter - 360442).Prime := by
  rw [fullRecordGapTerm01191_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01191, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01191_fast_pow_mod_ne_one

def fullRecordGapValue01192 : Nat := fullRecordGapCenterValue - 360292

theorem fullRecordGapTerm01192_eq_value :
    recordGapCenter - 360292 = fullRecordGapValue01192 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01192_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01192 (fullRecordGapValue01192 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01192_not_prime : ¬(recordGapCenter - 360292).Prime := by
  rw [fullRecordGapTerm01192_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01192, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01192_fast_pow_mod_ne_one

def fullRecordGapValue01193 : Nat := fullRecordGapCenterValue - 360268

theorem fullRecordGapTerm01193_eq_value :
    recordGapCenter - 360268 = fullRecordGapValue01193 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01193_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01193 (fullRecordGapValue01193 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01193_not_prime : ¬(recordGapCenter - 360268).Prime := by
  rw [fullRecordGapTerm01193_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01193, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01193_fast_pow_mod_ne_one

def fullRecordGapValue01194 : Nat := fullRecordGapCenterValue - 360222

theorem fullRecordGapTerm01194_eq_value :
    recordGapCenter - 360222 = fullRecordGapValue01194 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01194_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01194 (fullRecordGapValue01194 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01194_not_prime : ¬(recordGapCenter - 360222).Prime := by
  rw [fullRecordGapTerm01194_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01194, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01194_fast_pow_mod_ne_one

def fullRecordGapValue01195 : Nat := fullRecordGapCenterValue - 360154

theorem fullRecordGapTerm01195_eq_value :
    recordGapCenter - 360154 = fullRecordGapValue01195 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01195_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01195 (fullRecordGapValue01195 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01195_not_prime : ¬(recordGapCenter - 360154).Prime := by
  rw [fullRecordGapTerm01195_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01195, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01195_fast_pow_mod_ne_one

def fullRecordGapValue01196 : Nat := fullRecordGapCenterValue - 360124

theorem fullRecordGapTerm01196_eq_value :
    recordGapCenter - 360124 = fullRecordGapValue01196 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01196_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01196 (fullRecordGapValue01196 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01196_not_prime : ¬(recordGapCenter - 360124).Prime := by
  rw [fullRecordGapTerm01196_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01196, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01196_fast_pow_mod_ne_one

def fullRecordGapValue01197 : Nat := fullRecordGapCenterValue - 359998

theorem fullRecordGapTerm01197_eq_value :
    recordGapCenter - 359998 = fullRecordGapValue01197 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01197_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01197 (fullRecordGapValue01197 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01197_not_prime : ¬(recordGapCenter - 359998).Prime := by
  rw [fullRecordGapTerm01197_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01197, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01197_fast_pow_mod_ne_one

def fullRecordGapValue01198 : Nat := fullRecordGapCenterValue - 359938

theorem fullRecordGapTerm01198_eq_value :
    recordGapCenter - 359938 = fullRecordGapValue01198 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01198_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01198 (fullRecordGapValue01198 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01198_not_prime : ¬(recordGapCenter - 359938).Prime := by
  rw [fullRecordGapTerm01198_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01198, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01198_fast_pow_mod_ne_one

def fullRecordGapValue01199 : Nat := fullRecordGapCenterValue - 359914

theorem fullRecordGapTerm01199_eq_value :
    recordGapCenter - 359914 = fullRecordGapValue01199 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01199_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01199 (fullRecordGapValue01199 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01199_not_prime : ¬(recordGapCenter - 359914).Prime := by
  rw [fullRecordGapTerm01199_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01199, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01199_fast_pow_mod_ne_one

def fullRecordGapValue01200 : Nat := fullRecordGapCenterValue - 359908

theorem fullRecordGapTerm01200_eq_value :
    recordGapCenter - 359908 = fullRecordGapValue01200 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01200_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01200 (fullRecordGapValue01200 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01200_not_prime : ¬(recordGapCenter - 359908).Prime := by
  rw [fullRecordGapTerm01200_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01200, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01200_fast_pow_mod_ne_one

def fullRecordGapValue01201 : Nat := fullRecordGapCenterValue - 359692

theorem fullRecordGapTerm01201_eq_value :
    recordGapCenter - 359692 = fullRecordGapValue01201 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01201_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01201 (fullRecordGapValue01201 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01201_not_prime : ¬(recordGapCenter - 359692).Prime := by
  rw [fullRecordGapTerm01201_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01201, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01201_fast_pow_mod_ne_one

def fullRecordGapValue01202 : Nat := fullRecordGapCenterValue - 359614

theorem fullRecordGapTerm01202_eq_value :
    recordGapCenter - 359614 = fullRecordGapValue01202 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01202_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01202 (fullRecordGapValue01202 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01202_not_prime : ¬(recordGapCenter - 359614).Prime := by
  rw [fullRecordGapTerm01202_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01202, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01202_fast_pow_mod_ne_one

def fullRecordGapValue01203 : Nat := fullRecordGapCenterValue - 359182

theorem fullRecordGapTerm01203_eq_value :
    recordGapCenter - 359182 = fullRecordGapValue01203 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01203_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01203 (fullRecordGapValue01203 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01203_not_prime : ¬(recordGapCenter - 359182).Prime := by
  rw [fullRecordGapTerm01203_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01203, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01203_fast_pow_mod_ne_one

def fullRecordGapValue01204 : Nat := fullRecordGapCenterValue - 359068

theorem fullRecordGapTerm01204_eq_value :
    recordGapCenter - 359068 = fullRecordGapValue01204 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01204_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01204 (fullRecordGapValue01204 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01204_not_prime : ¬(recordGapCenter - 359068).Prime := by
  rw [fullRecordGapTerm01204_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01204, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01204_fast_pow_mod_ne_one

def fullRecordGapValue01205 : Nat := fullRecordGapCenterValue - 358942

theorem fullRecordGapTerm01205_eq_value :
    recordGapCenter - 358942 = fullRecordGapValue01205 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01205_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01205 (fullRecordGapValue01205 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01205_not_prime : ¬(recordGapCenter - 358942).Prime := by
  rw [fullRecordGapTerm01205_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01205, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01205_fast_pow_mod_ne_one

def fullRecordGapValue01206 : Nat := fullRecordGapCenterValue - 358854

theorem fullRecordGapTerm01206_eq_value :
    recordGapCenter - 358854 = fullRecordGapValue01206 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01206_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01206 (fullRecordGapValue01206 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01206_not_prime : ¬(recordGapCenter - 358854).Prime := by
  rw [fullRecordGapTerm01206_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01206, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01206_fast_pow_mod_ne_one

def fullRecordGapValue01207 : Nat := fullRecordGapCenterValue - 358762

theorem fullRecordGapTerm01207_eq_value :
    recordGapCenter - 358762 = fullRecordGapValue01207 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01207_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01207 (fullRecordGapValue01207 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01207_not_prime : ¬(recordGapCenter - 358762).Prime := by
  rw [fullRecordGapTerm01207_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01207, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01207_fast_pow_mod_ne_one

def fullRecordGapValue01208 : Nat := fullRecordGapCenterValue - 358738

theorem fullRecordGapTerm01208_eq_value :
    recordGapCenter - 358738 = fullRecordGapValue01208 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01208_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01208 (fullRecordGapValue01208 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01208_not_prime : ¬(recordGapCenter - 358738).Prime := by
  rw [fullRecordGapTerm01208_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01208, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01208_fast_pow_mod_ne_one

def fullRecordGapValue01209 : Nat := fullRecordGapCenterValue - 358684

theorem fullRecordGapTerm01209_eq_value :
    recordGapCenter - 358684 = fullRecordGapValue01209 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01209_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01209 (fullRecordGapValue01209 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01209_not_prime : ¬(recordGapCenter - 358684).Prime := by
  rw [fullRecordGapTerm01209_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01209, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01209_fast_pow_mod_ne_one

def fullRecordGapValue01210 : Nat := fullRecordGapCenterValue - 358642

theorem fullRecordGapTerm01210_eq_value :
    recordGapCenter - 358642 = fullRecordGapValue01210 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01210_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01210 (fullRecordGapValue01210 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01210_not_prime : ¬(recordGapCenter - 358642).Prime := by
  rw [fullRecordGapTerm01210_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01210, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01210_fast_pow_mod_ne_one

def fullRecordGapValue01211 : Nat := fullRecordGapCenterValue - 358522

theorem fullRecordGapTerm01211_eq_value :
    recordGapCenter - 358522 = fullRecordGapValue01211 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01211_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01211 (fullRecordGapValue01211 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01211_not_prime : ¬(recordGapCenter - 358522).Prime := by
  rw [fullRecordGapTerm01211_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01211, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01211_fast_pow_mod_ne_one

def fullRecordGapValue01212 : Nat := fullRecordGapCenterValue - 358482

theorem fullRecordGapTerm01212_eq_value :
    recordGapCenter - 358482 = fullRecordGapValue01212 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01212_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01212 (fullRecordGapValue01212 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01212_not_prime : ¬(recordGapCenter - 358482).Prime := by
  rw [fullRecordGapTerm01212_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01212, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01212_fast_pow_mod_ne_one

def fullRecordGapValue01213 : Nat := fullRecordGapCenterValue - 358458

theorem fullRecordGapTerm01213_eq_value :
    recordGapCenter - 358458 = fullRecordGapValue01213 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01213_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01213 (fullRecordGapValue01213 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01213_not_prime : ¬(recordGapCenter - 358458).Prime := by
  rw [fullRecordGapTerm01213_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01213, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01213_fast_pow_mod_ne_one

def fullRecordGapValue01214 : Nat := fullRecordGapCenterValue - 358444

theorem fullRecordGapTerm01214_eq_value :
    recordGapCenter - 358444 = fullRecordGapValue01214 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01214_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01214 (fullRecordGapValue01214 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01214_not_prime : ¬(recordGapCenter - 358444).Prime := by
  rw [fullRecordGapTerm01214_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01214, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01214_fast_pow_mod_ne_one

def fullRecordGapValue01215 : Nat := fullRecordGapCenterValue - 358374

theorem fullRecordGapTerm01215_eq_value :
    recordGapCenter - 358374 = fullRecordGapValue01215 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01215_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01215 (fullRecordGapValue01215 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01215_not_prime : ¬(recordGapCenter - 358374).Prime := by
  rw [fullRecordGapTerm01215_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01215, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01215_fast_pow_mod_ne_one

def fullRecordGapValue01216 : Nat := fullRecordGapCenterValue - 358312

theorem fullRecordGapTerm01216_eq_value :
    recordGapCenter - 358312 = fullRecordGapValue01216 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01216_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01216 (fullRecordGapValue01216 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01216_not_prime : ¬(recordGapCenter - 358312).Prime := by
  rw [fullRecordGapTerm01216_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01216, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01216_fast_pow_mod_ne_one

def fullRecordGapValue01217 : Nat := fullRecordGapCenterValue - 358222

theorem fullRecordGapTerm01217_eq_value :
    recordGapCenter - 358222 = fullRecordGapValue01217 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01217_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01217 (fullRecordGapValue01217 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01217_not_prime : ¬(recordGapCenter - 358222).Prime := by
  rw [fullRecordGapTerm01217_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01217, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01217_fast_pow_mod_ne_one

def fullRecordGapValue01218 : Nat := fullRecordGapCenterValue - 358108

theorem fullRecordGapTerm01218_eq_value :
    recordGapCenter - 358108 = fullRecordGapValue01218 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01218_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01218 (fullRecordGapValue01218 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01218_not_prime : ¬(recordGapCenter - 358108).Prime := by
  rw [fullRecordGapTerm01218_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01218, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01218_fast_pow_mod_ne_one

def fullRecordGapValue01219 : Nat := fullRecordGapCenterValue - 358042

theorem fullRecordGapTerm01219_eq_value :
    recordGapCenter - 358042 = fullRecordGapValue01219 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01219_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01219 (fullRecordGapValue01219 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01219_not_prime : ¬(recordGapCenter - 358042).Prime := by
  rw [fullRecordGapTerm01219_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01219, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01219_fast_pow_mod_ne_one

def fullRecordGapValue01220 : Nat := fullRecordGapCenterValue - 357772

theorem fullRecordGapTerm01220_eq_value :
    recordGapCenter - 357772 = fullRecordGapValue01220 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01220_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01220 (fullRecordGapValue01220 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01220_not_prime : ¬(recordGapCenter - 357772).Prime := by
  rw [fullRecordGapTerm01220_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01220, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01220_fast_pow_mod_ne_one

def fullRecordGapValue01221 : Nat := fullRecordGapCenterValue - 357762

theorem fullRecordGapTerm01221_eq_value :
    recordGapCenter - 357762 = fullRecordGapValue01221 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01221_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01221 (fullRecordGapValue01221 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01221_not_prime : ¬(recordGapCenter - 357762).Prime := by
  rw [fullRecordGapTerm01221_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01221, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01221_fast_pow_mod_ne_one

def fullRecordGapValue01222 : Nat := fullRecordGapCenterValue - 357718

theorem fullRecordGapTerm01222_eq_value :
    recordGapCenter - 357718 = fullRecordGapValue01222 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01222_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01222 (fullRecordGapValue01222 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01222_not_prime : ¬(recordGapCenter - 357718).Prime := by
  rw [fullRecordGapTerm01222_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01222, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01222_fast_pow_mod_ne_one

def fullRecordGapValue01223 : Nat := fullRecordGapCenterValue - 357402

theorem fullRecordGapTerm01223_eq_value :
    recordGapCenter - 357402 = fullRecordGapValue01223 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01223_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01223 (fullRecordGapValue01223 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01223_not_prime : ¬(recordGapCenter - 357402).Prime := by
  rw [fullRecordGapTerm01223_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01223, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01223_fast_pow_mod_ne_one

def fullRecordGapValue01224 : Nat := fullRecordGapCenterValue - 357342

theorem fullRecordGapTerm01224_eq_value :
    recordGapCenter - 357342 = fullRecordGapValue01224 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01224_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01224 (fullRecordGapValue01224 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01224_not_prime : ¬(recordGapCenter - 357342).Prime := by
  rw [fullRecordGapTerm01224_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01224, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01224_fast_pow_mod_ne_one

def fullRecordGapValue01225 : Nat := fullRecordGapCenterValue - 357268

theorem fullRecordGapTerm01225_eq_value :
    recordGapCenter - 357268 = fullRecordGapValue01225 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01225_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01225 (fullRecordGapValue01225 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01225_not_prime : ¬(recordGapCenter - 357268).Prime := by
  rw [fullRecordGapTerm01225_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01225, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01225_fast_pow_mod_ne_one

def fullRecordGapValue01226 : Nat := fullRecordGapCenterValue - 357234

theorem fullRecordGapTerm01226_eq_value :
    recordGapCenter - 357234 = fullRecordGapValue01226 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01226_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01226 (fullRecordGapValue01226 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01226_not_prime : ¬(recordGapCenter - 357234).Prime := by
  rw [fullRecordGapTerm01226_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01226, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01226_fast_pow_mod_ne_one

def fullRecordGapValue01227 : Nat := fullRecordGapCenterValue - 357208

theorem fullRecordGapTerm01227_eq_value :
    recordGapCenter - 357208 = fullRecordGapValue01227 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01227_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01227 (fullRecordGapValue01227 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01227_not_prime : ¬(recordGapCenter - 357208).Prime := by
  rw [fullRecordGapTerm01227_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01227, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01227_fast_pow_mod_ne_one

def fullRecordGapValue01228 : Nat := fullRecordGapCenterValue - 357202

theorem fullRecordGapTerm01228_eq_value :
    recordGapCenter - 357202 = fullRecordGapValue01228 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01228_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01228 (fullRecordGapValue01228 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01228_not_prime : ¬(recordGapCenter - 357202).Prime := by
  rw [fullRecordGapTerm01228_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01228, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01228_fast_pow_mod_ne_one

def fullRecordGapValue01229 : Nat := fullRecordGapCenterValue - 356982

theorem fullRecordGapTerm01229_eq_value :
    recordGapCenter - 356982 = fullRecordGapValue01229 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01229_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01229 (fullRecordGapValue01229 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01229_not_prime : ¬(recordGapCenter - 356982).Prime := by
  rw [fullRecordGapTerm01229_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01229, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01229_fast_pow_mod_ne_one

def fullRecordGapValue01230 : Nat := fullRecordGapCenterValue - 356974

theorem fullRecordGapTerm01230_eq_value :
    recordGapCenter - 356974 = fullRecordGapValue01230 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01230_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01230 (fullRecordGapValue01230 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01230_not_prime : ¬(recordGapCenter - 356974).Prime := by
  rw [fullRecordGapTerm01230_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01230, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01230_fast_pow_mod_ne_one

def fullRecordGapValue01231 : Nat := fullRecordGapCenterValue - 356962

theorem fullRecordGapTerm01231_eq_value :
    recordGapCenter - 356962 = fullRecordGapValue01231 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01231_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01231 (fullRecordGapValue01231 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01231_not_prime : ¬(recordGapCenter - 356962).Prime := by
  rw [fullRecordGapTerm01231_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01231, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01231_fast_pow_mod_ne_one

def fullRecordGapValue01232 : Nat := fullRecordGapCenterValue - 356838

theorem fullRecordGapTerm01232_eq_value :
    recordGapCenter - 356838 = fullRecordGapValue01232 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01232_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01232 (fullRecordGapValue01232 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01232_not_prime : ¬(recordGapCenter - 356838).Prime := by
  rw [fullRecordGapTerm01232_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01232, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01232_fast_pow_mod_ne_one

def fullRecordGapValue01233 : Nat := fullRecordGapCenterValue - 356802

theorem fullRecordGapTerm01233_eq_value :
    recordGapCenter - 356802 = fullRecordGapValue01233 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01233_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01233 (fullRecordGapValue01233 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01233_not_prime : ¬(recordGapCenter - 356802).Prime := by
  rw [fullRecordGapTerm01233_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01233, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01233_fast_pow_mod_ne_one

def fullRecordGapValue01234 : Nat := fullRecordGapCenterValue - 356722

theorem fullRecordGapTerm01234_eq_value :
    recordGapCenter - 356722 = fullRecordGapValue01234 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01234_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01234 (fullRecordGapValue01234 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01234_not_prime : ¬(recordGapCenter - 356722).Prime := by
  rw [fullRecordGapTerm01234_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01234, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01234_fast_pow_mod_ne_one

def fullRecordGapValue01235 : Nat := fullRecordGapCenterValue - 356718

theorem fullRecordGapTerm01235_eq_value :
    recordGapCenter - 356718 = fullRecordGapValue01235 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01235_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01235 (fullRecordGapValue01235 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01235_not_prime : ¬(recordGapCenter - 356718).Prime := by
  rw [fullRecordGapTerm01235_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01235, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01235_fast_pow_mod_ne_one

def fullRecordGapValue01236 : Nat := fullRecordGapCenterValue - 356614

theorem fullRecordGapTerm01236_eq_value :
    recordGapCenter - 356614 = fullRecordGapValue01236 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01236_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01236 (fullRecordGapValue01236 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01236_not_prime : ¬(recordGapCenter - 356614).Prime := by
  rw [fullRecordGapTerm01236_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01236, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01236_fast_pow_mod_ne_one

def fullRecordGapValue01237 : Nat := fullRecordGapCenterValue - 356502

theorem fullRecordGapTerm01237_eq_value :
    recordGapCenter - 356502 = fullRecordGapValue01237 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01237_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01237 (fullRecordGapValue01237 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01237_not_prime : ¬(recordGapCenter - 356502).Prime := by
  rw [fullRecordGapTerm01237_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01237, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01237_fast_pow_mod_ne_one

def fullRecordGapValue01238 : Nat := fullRecordGapCenterValue - 356494

theorem fullRecordGapTerm01238_eq_value :
    recordGapCenter - 356494 = fullRecordGapValue01238 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01238_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01238 (fullRecordGapValue01238 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01238_not_prime : ¬(recordGapCenter - 356494).Prime := by
  rw [fullRecordGapTerm01238_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01238, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01238_fast_pow_mod_ne_one

def fullRecordGapValue01239 : Nat := fullRecordGapCenterValue - 356400

theorem fullRecordGapTerm01239_eq_value :
    recordGapCenter - 356400 = fullRecordGapValue01239 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01239_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01239 (fullRecordGapValue01239 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01239_not_prime : ¬(recordGapCenter - 356400).Prime := by
  rw [fullRecordGapTerm01239_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01239, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01239_fast_pow_mod_ne_one

def fullRecordGapValue01240 : Nat := fullRecordGapCenterValue - 356394

theorem fullRecordGapTerm01240_eq_value :
    recordGapCenter - 356394 = fullRecordGapValue01240 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01240_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01240 (fullRecordGapValue01240 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01240_not_prime : ¬(recordGapCenter - 356394).Prime := by
  rw [fullRecordGapTerm01240_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01240, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01240_fast_pow_mod_ne_one

def fullRecordGapValue01241 : Nat := fullRecordGapCenterValue - 356374

theorem fullRecordGapTerm01241_eq_value :
    recordGapCenter - 356374 = fullRecordGapValue01241 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01241_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01241 (fullRecordGapValue01241 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01241_not_prime : ¬(recordGapCenter - 356374).Prime := by
  rw [fullRecordGapTerm01241_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01241, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01241_fast_pow_mod_ne_one

def fullRecordGapValue01242 : Nat := fullRecordGapCenterValue - 356262

theorem fullRecordGapTerm01242_eq_value :
    recordGapCenter - 356262 = fullRecordGapValue01242 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01242_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01242 (fullRecordGapValue01242 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01242_not_prime : ¬(recordGapCenter - 356262).Prime := by
  rw [fullRecordGapTerm01242_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01242, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01242_fast_pow_mod_ne_one

def fullRecordGapValue01243 : Nat := fullRecordGapCenterValue - 356248

theorem fullRecordGapTerm01243_eq_value :
    recordGapCenter - 356248 = fullRecordGapValue01243 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01243_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01243 (fullRecordGapValue01243 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01243_not_prime : ¬(recordGapCenter - 356248).Prime := by
  rw [fullRecordGapTerm01243_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01243, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01243_fast_pow_mod_ne_one

def fullRecordGapValue01244 : Nat := fullRecordGapCenterValue - 356214

theorem fullRecordGapTerm01244_eq_value :
    recordGapCenter - 356214 = fullRecordGapValue01244 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01244_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01244 (fullRecordGapValue01244 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01244_not_prime : ¬(recordGapCenter - 356214).Prime := by
  rw [fullRecordGapTerm01244_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01244, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01244_fast_pow_mod_ne_one

def fullRecordGapValue01245 : Nat := fullRecordGapCenterValue - 356164

theorem fullRecordGapTerm01245_eq_value :
    recordGapCenter - 356164 = fullRecordGapValue01245 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01245_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01245 (fullRecordGapValue01245 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01245_not_prime : ¬(recordGapCenter - 356164).Prime := by
  rw [fullRecordGapTerm01245_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01245, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01245_fast_pow_mod_ne_one

def fullRecordGapValue01246 : Nat := fullRecordGapCenterValue - 356142

theorem fullRecordGapTerm01246_eq_value :
    recordGapCenter - 356142 = fullRecordGapValue01246 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01246_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01246 (fullRecordGapValue01246 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01246_not_prime : ¬(recordGapCenter - 356142).Prime := by
  rw [fullRecordGapTerm01246_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01246, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01246_fast_pow_mod_ne_one

def fullRecordGapValue01247 : Nat := fullRecordGapCenterValue - 356002

theorem fullRecordGapTerm01247_eq_value :
    recordGapCenter - 356002 = fullRecordGapValue01247 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01247_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01247 (fullRecordGapValue01247 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01247_not_prime : ¬(recordGapCenter - 356002).Prime := by
  rw [fullRecordGapTerm01247_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01247, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01247_fast_pow_mod_ne_one

def fullRecordGapValue01248 : Nat := fullRecordGapCenterValue - 355998

theorem fullRecordGapTerm01248_eq_value :
    recordGapCenter - 355998 = fullRecordGapValue01248 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01248_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01248 (fullRecordGapValue01248 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01248_not_prime : ¬(recordGapCenter - 355998).Prime := by
  rw [fullRecordGapTerm01248_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01248, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01248_fast_pow_mod_ne_one

def fullRecordGapValue01249 : Nat := fullRecordGapCenterValue - 355864

theorem fullRecordGapTerm01249_eq_value :
    recordGapCenter - 355864 = fullRecordGapValue01249 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01249_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01249 (fullRecordGapValue01249 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01249_not_prime : ¬(recordGapCenter - 355864).Prime := by
  rw [fullRecordGapTerm01249_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01249, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01249_fast_pow_mod_ne_one

def fullRecordGapValue01250 : Nat := fullRecordGapCenterValue - 355858

theorem fullRecordGapTerm01250_eq_value :
    recordGapCenter - 355858 = fullRecordGapValue01250 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01250_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01250 (fullRecordGapValue01250 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01250_not_prime : ¬(recordGapCenter - 355858).Prime := by
  rw [fullRecordGapTerm01250_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01250, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01250_fast_pow_mod_ne_one

def fullRecordGapValue01251 : Nat := fullRecordGapCenterValue - 355582

theorem fullRecordGapTerm01251_eq_value :
    recordGapCenter - 355582 = fullRecordGapValue01251 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01251_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01251 (fullRecordGapValue01251 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01251_not_prime : ¬(recordGapCenter - 355582).Prime := by
  rw [fullRecordGapTerm01251_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01251, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01251_fast_pow_mod_ne_one

def fullRecordGapValue01252 : Nat := fullRecordGapCenterValue - 355492

theorem fullRecordGapTerm01252_eq_value :
    recordGapCenter - 355492 = fullRecordGapValue01252 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01252_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01252 (fullRecordGapValue01252 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01252_not_prime : ¬(recordGapCenter - 355492).Prime := by
  rw [fullRecordGapTerm01252_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01252, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01252_fast_pow_mod_ne_one

def fullRecordGapValue01253 : Nat := fullRecordGapCenterValue - 355444

theorem fullRecordGapTerm01253_eq_value :
    recordGapCenter - 355444 = fullRecordGapValue01253 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01253_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01253 (fullRecordGapValue01253 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01253_not_prime : ¬(recordGapCenter - 355444).Prime := by
  rw [fullRecordGapTerm01253_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01253, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01253_fast_pow_mod_ne_one

def fullRecordGapValue01254 : Nat := fullRecordGapCenterValue - 355434

theorem fullRecordGapTerm01254_eq_value :
    recordGapCenter - 355434 = fullRecordGapValue01254 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01254_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01254 (fullRecordGapValue01254 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01254_not_prime : ¬(recordGapCenter - 355434).Prime := by
  rw [fullRecordGapTerm01254_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01254, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01254_fast_pow_mod_ne_one

def fullRecordGapValue01255 : Nat := fullRecordGapCenterValue - 355294

theorem fullRecordGapTerm01255_eq_value :
    recordGapCenter - 355294 = fullRecordGapValue01255 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01255_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01255 (fullRecordGapValue01255 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01255_not_prime : ¬(recordGapCenter - 355294).Prime := by
  rw [fullRecordGapTerm01255_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01255, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01255_fast_pow_mod_ne_one

def fullRecordGapValue01256 : Nat := fullRecordGapCenterValue - 355254

theorem fullRecordGapTerm01256_eq_value :
    recordGapCenter - 355254 = fullRecordGapValue01256 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01256_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01256 (fullRecordGapValue01256 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01256_not_prime : ¬(recordGapCenter - 355254).Prime := by
  rw [fullRecordGapTerm01256_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01256, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01256_fast_pow_mod_ne_one

def fullRecordGapValue01257 : Nat := fullRecordGapCenterValue - 355252

theorem fullRecordGapTerm01257_eq_value :
    recordGapCenter - 355252 = fullRecordGapValue01257 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01257_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01257 (fullRecordGapValue01257 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01257_not_prime : ¬(recordGapCenter - 355252).Prime := by
  rw [fullRecordGapTerm01257_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01257, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01257_fast_pow_mod_ne_one

def fullRecordGapValue01258 : Nat := fullRecordGapCenterValue - 355242

theorem fullRecordGapTerm01258_eq_value :
    recordGapCenter - 355242 = fullRecordGapValue01258 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01258_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01258 (fullRecordGapValue01258 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01258_not_prime : ¬(recordGapCenter - 355242).Prime := by
  rw [fullRecordGapTerm01258_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01258, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01258_fast_pow_mod_ne_one

def fullRecordGapValue01259 : Nat := fullRecordGapCenterValue - 355228

theorem fullRecordGapTerm01259_eq_value :
    recordGapCenter - 355228 = fullRecordGapValue01259 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01259_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01259 (fullRecordGapValue01259 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01259_not_prime : ¬(recordGapCenter - 355228).Prime := by
  rw [fullRecordGapTerm01259_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01259, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01259_fast_pow_mod_ne_one

def fullRecordGapValue01260 : Nat := fullRecordGapCenterValue - 355098

theorem fullRecordGapTerm01260_eq_value :
    recordGapCenter - 355098 = fullRecordGapValue01260 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01260_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01260 (fullRecordGapValue01260 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01260_not_prime : ¬(recordGapCenter - 355098).Prime := by
  rw [fullRecordGapTerm01260_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01260, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01260_fast_pow_mod_ne_one

def fullRecordGapValue01261 : Nat := fullRecordGapCenterValue - 355078

theorem fullRecordGapTerm01261_eq_value :
    recordGapCenter - 355078 = fullRecordGapValue01261 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01261_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01261 (fullRecordGapValue01261 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01261_not_prime : ¬(recordGapCenter - 355078).Prime := by
  rw [fullRecordGapTerm01261_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01261, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01261_fast_pow_mod_ne_one

def fullRecordGapValue01262 : Nat := fullRecordGapCenterValue - 354988

theorem fullRecordGapTerm01262_eq_value :
    recordGapCenter - 354988 = fullRecordGapValue01262 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01262_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01262 (fullRecordGapValue01262 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01262_not_prime : ¬(recordGapCenter - 354988).Prime := by
  rw [fullRecordGapTerm01262_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01262, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01262_fast_pow_mod_ne_one

def fullRecordGapValue01263 : Nat := fullRecordGapCenterValue - 354808

theorem fullRecordGapTerm01263_eq_value :
    recordGapCenter - 354808 = fullRecordGapValue01263 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01263_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01263 (fullRecordGapValue01263 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01263_not_prime : ¬(recordGapCenter - 354808).Prime := by
  rw [fullRecordGapTerm01263_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01263, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01263_fast_pow_mod_ne_one

def fullRecordGapValue01264 : Nat := fullRecordGapCenterValue - 354724

theorem fullRecordGapTerm01264_eq_value :
    recordGapCenter - 354724 = fullRecordGapValue01264 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01264_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01264 (fullRecordGapValue01264 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01264_not_prime : ¬(recordGapCenter - 354724).Prime := by
  rw [fullRecordGapTerm01264_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01264, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01264_fast_pow_mod_ne_one

def fullRecordGapValue01265 : Nat := fullRecordGapCenterValue - 354652

theorem fullRecordGapTerm01265_eq_value :
    recordGapCenter - 354652 = fullRecordGapValue01265 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01265_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01265 (fullRecordGapValue01265 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01265_not_prime : ¬(recordGapCenter - 354652).Prime := by
  rw [fullRecordGapTerm01265_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01265, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01265_fast_pow_mod_ne_one

def fullRecordGapValue01266 : Nat := fullRecordGapCenterValue - 354604

theorem fullRecordGapTerm01266_eq_value :
    recordGapCenter - 354604 = fullRecordGapValue01266 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01266_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01266 (fullRecordGapValue01266 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01266_not_prime : ¬(recordGapCenter - 354604).Prime := by
  rw [fullRecordGapTerm01266_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01266, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01266_fast_pow_mod_ne_one

def fullRecordGapValue01267 : Nat := fullRecordGapCenterValue - 354538

theorem fullRecordGapTerm01267_eq_value :
    recordGapCenter - 354538 = fullRecordGapValue01267 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01267_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01267 (fullRecordGapValue01267 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01267_not_prime : ¬(recordGapCenter - 354538).Prime := by
  rw [fullRecordGapTerm01267_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01267, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01267_fast_pow_mod_ne_one

def fullRecordGapValue01268 : Nat := fullRecordGapCenterValue - 354478

theorem fullRecordGapTerm01268_eq_value :
    recordGapCenter - 354478 = fullRecordGapValue01268 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01268_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01268 (fullRecordGapValue01268 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01268_not_prime : ¬(recordGapCenter - 354478).Prime := by
  rw [fullRecordGapTerm01268_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01268, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01268_fast_pow_mod_ne_one

def fullRecordGapValue01269 : Nat := fullRecordGapCenterValue - 354378

theorem fullRecordGapTerm01269_eq_value :
    recordGapCenter - 354378 = fullRecordGapValue01269 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01269_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01269 (fullRecordGapValue01269 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01269_not_prime : ¬(recordGapCenter - 354378).Prime := by
  rw [fullRecordGapTerm01269_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01269, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01269_fast_pow_mod_ne_one

def fullRecordGapValue01270 : Nat := fullRecordGapCenterValue - 354364

theorem fullRecordGapTerm01270_eq_value :
    recordGapCenter - 354364 = fullRecordGapValue01270 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01270_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01270 (fullRecordGapValue01270 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01270_not_prime : ¬(recordGapCenter - 354364).Prime := by
  rw [fullRecordGapTerm01270_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01270, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01270_fast_pow_mod_ne_one

def fullRecordGapValue01271 : Nat := fullRecordGapCenterValue - 354294

theorem fullRecordGapTerm01271_eq_value :
    recordGapCenter - 354294 = fullRecordGapValue01271 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01271_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01271 (fullRecordGapValue01271 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01271_not_prime : ¬(recordGapCenter - 354294).Prime := by
  rw [fullRecordGapTerm01271_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01271, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01271_fast_pow_mod_ne_one

def fullRecordGapValue01272 : Nat := fullRecordGapCenterValue - 354232

theorem fullRecordGapTerm01272_eq_value :
    recordGapCenter - 354232 = fullRecordGapValue01272 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01272_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01272 (fullRecordGapValue01272 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01272_not_prime : ¬(recordGapCenter - 354232).Prime := by
  rw [fullRecordGapTerm01272_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01272, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01272_fast_pow_mod_ne_one

def fullRecordGapValue01273 : Nat := fullRecordGapCenterValue - 354202

theorem fullRecordGapTerm01273_eq_value :
    recordGapCenter - 354202 = fullRecordGapValue01273 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01273_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01273 (fullRecordGapValue01273 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01273_not_prime : ¬(recordGapCenter - 354202).Prime := by
  rw [fullRecordGapTerm01273_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01273, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01273_fast_pow_mod_ne_one

def fullRecordGapValue01274 : Nat := fullRecordGapCenterValue - 354184

theorem fullRecordGapTerm01274_eq_value :
    recordGapCenter - 354184 = fullRecordGapValue01274 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01274_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01274 (fullRecordGapValue01274 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01274_not_prime : ¬(recordGapCenter - 354184).Prime := by
  rw [fullRecordGapTerm01274_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01274, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01274_fast_pow_mod_ne_one

def fullRecordGapValue01275 : Nat := fullRecordGapCenterValue - 354174

theorem fullRecordGapTerm01275_eq_value :
    recordGapCenter - 354174 = fullRecordGapValue01275 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01275_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01275 (fullRecordGapValue01275 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01275_not_prime : ¬(recordGapCenter - 354174).Prime := by
  rw [fullRecordGapTerm01275_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01275, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01275_fast_pow_mod_ne_one

def fullRecordGapValue01276 : Nat := fullRecordGapCenterValue - 354052

theorem fullRecordGapTerm01276_eq_value :
    recordGapCenter - 354052 = fullRecordGapValue01276 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01276_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01276 (fullRecordGapValue01276 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01276_not_prime : ¬(recordGapCenter - 354052).Prime := by
  rw [fullRecordGapTerm01276_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01276, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01276_fast_pow_mod_ne_one

def fullRecordGapValue01277 : Nat := fullRecordGapCenterValue - 353902

theorem fullRecordGapTerm01277_eq_value :
    recordGapCenter - 353902 = fullRecordGapValue01277 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01277_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01277 (fullRecordGapValue01277 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01277_not_prime : ¬(recordGapCenter - 353902).Prime := by
  rw [fullRecordGapTerm01277_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01277, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01277_fast_pow_mod_ne_one

def fullRecordGapValue01278 : Nat := fullRecordGapCenterValue - 353692

theorem fullRecordGapTerm01278_eq_value :
    recordGapCenter - 353692 = fullRecordGapValue01278 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01278_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01278 (fullRecordGapValue01278 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01278_not_prime : ¬(recordGapCenter - 353692).Prime := by
  rw [fullRecordGapTerm01278_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01278, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01278_fast_pow_mod_ne_one

def fullRecordGapValue01279 : Nat := fullRecordGapCenterValue - 353638

theorem fullRecordGapTerm01279_eq_value :
    recordGapCenter - 353638 = fullRecordGapValue01279 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01279_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01279 (fullRecordGapValue01279 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01279_not_prime : ¬(recordGapCenter - 353638).Prime := by
  rw [fullRecordGapTerm01279_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01279, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01279_fast_pow_mod_ne_one

def fullRecordGapValue01280 : Nat := fullRecordGapCenterValue - 353512

theorem fullRecordGapTerm01280_eq_value :
    recordGapCenter - 353512 = fullRecordGapValue01280 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01280_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01280 (fullRecordGapValue01280 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01280_not_prime : ¬(recordGapCenter - 353512).Prime := by
  rw [fullRecordGapTerm01280_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01280, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01280_fast_pow_mod_ne_one

end PrimeFactorUnimodality
