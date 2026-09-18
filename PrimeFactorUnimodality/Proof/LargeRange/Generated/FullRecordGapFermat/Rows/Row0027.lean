import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue06657 : Nat := fullRecordGapCenterValue + 368582

theorem fullRecordGapTerm06657_eq_value :
    recordGapCenter + 368582 = fullRecordGapValue06657 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06657_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06657 (fullRecordGapValue06657 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06657_not_prime : ¬(recordGapCenter + 368582).Prime := by
  rw [fullRecordGapTerm06657_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06657, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06657_fast_pow_mod_ne_one

def fullRecordGapValue06658 : Nat := fullRecordGapCenterValue + 368618

theorem fullRecordGapTerm06658_eq_value :
    recordGapCenter + 368618 = fullRecordGapValue06658 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06658_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06658 (fullRecordGapValue06658 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06658_not_prime : ¬(recordGapCenter + 368618).Prime := by
  rw [fullRecordGapTerm06658_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06658, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06658_fast_pow_mod_ne_one

def fullRecordGapValue06659 : Nat := fullRecordGapCenterValue + 368642

theorem fullRecordGapTerm06659_eq_value :
    recordGapCenter + 368642 = fullRecordGapValue06659 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06659_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06659 (fullRecordGapValue06659 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06659_not_prime : ¬(recordGapCenter + 368642).Prime := by
  rw [fullRecordGapTerm06659_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06659, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06659_fast_pow_mod_ne_one

def fullRecordGapValue06660 : Nat := fullRecordGapCenterValue + 368666

theorem fullRecordGapTerm06660_eq_value :
    recordGapCenter + 368666 = fullRecordGapValue06660 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06660_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06660 (fullRecordGapValue06660 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06660_not_prime : ¬(recordGapCenter + 368666).Prime := by
  rw [fullRecordGapTerm06660_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06660, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06660_fast_pow_mod_ne_one

def fullRecordGapValue06661 : Nat := fullRecordGapCenterValue + 368898

theorem fullRecordGapTerm06661_eq_value :
    recordGapCenter + 368898 = fullRecordGapValue06661 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06661_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06661 (fullRecordGapValue06661 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06661_not_prime : ¬(recordGapCenter + 368898).Prime := by
  rw [fullRecordGapTerm06661_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06661, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06661_fast_pow_mod_ne_one

def fullRecordGapValue06662 : Nat := fullRecordGapCenterValue + 368972

theorem fullRecordGapTerm06662_eq_value :
    recordGapCenter + 368972 = fullRecordGapValue06662 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06662_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06662 (fullRecordGapValue06662 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06662_not_prime : ¬(recordGapCenter + 368972).Prime := by
  rw [fullRecordGapTerm06662_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06662, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06662_fast_pow_mod_ne_one

def fullRecordGapValue06663 : Nat := fullRecordGapCenterValue + 369128

theorem fullRecordGapTerm06663_eq_value :
    recordGapCenter + 369128 = fullRecordGapValue06663 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06663_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06663 (fullRecordGapValue06663 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06663_not_prime : ¬(recordGapCenter + 369128).Prime := by
  rw [fullRecordGapTerm06663_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06663, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06663_fast_pow_mod_ne_one

def fullRecordGapValue06664 : Nat := fullRecordGapCenterValue + 369218

theorem fullRecordGapTerm06664_eq_value :
    recordGapCenter + 369218 = fullRecordGapValue06664 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06664_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06664 (fullRecordGapValue06664 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06664_not_prime : ¬(recordGapCenter + 369218).Prime := by
  rw [fullRecordGapTerm06664_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06664, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06664_fast_pow_mod_ne_one

def fullRecordGapValue06665 : Nat := fullRecordGapCenterValue + 369302

theorem fullRecordGapTerm06665_eq_value :
    recordGapCenter + 369302 = fullRecordGapValue06665 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06665_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06665 (fullRecordGapValue06665 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06665_not_prime : ¬(recordGapCenter + 369302).Prime := by
  rw [fullRecordGapTerm06665_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06665, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06665_fast_pow_mod_ne_one

def fullRecordGapValue06666 : Nat := fullRecordGapCenterValue + 369428

theorem fullRecordGapTerm06666_eq_value :
    recordGapCenter + 369428 = fullRecordGapValue06666 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06666_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06666 (fullRecordGapValue06666 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06666_not_prime : ¬(recordGapCenter + 369428).Prime := by
  rw [fullRecordGapTerm06666_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06666, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06666_fast_pow_mod_ne_one

def fullRecordGapValue06667 : Nat := fullRecordGapCenterValue + 369476

theorem fullRecordGapTerm06667_eq_value :
    recordGapCenter + 369476 = fullRecordGapValue06667 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06667_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06667 (fullRecordGapValue06667 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06667_not_prime : ¬(recordGapCenter + 369476).Prime := by
  rw [fullRecordGapTerm06667_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06667, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06667_fast_pow_mod_ne_one

def fullRecordGapValue06668 : Nat := fullRecordGapCenterValue + 369506

theorem fullRecordGapTerm06668_eq_value :
    recordGapCenter + 369506 = fullRecordGapValue06668 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06668_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06668 (fullRecordGapValue06668 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06668_not_prime : ¬(recordGapCenter + 369506).Prime := by
  rw [fullRecordGapTerm06668_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06668, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06668_fast_pow_mod_ne_one

def fullRecordGapValue06669 : Nat := fullRecordGapCenterValue + 369752

theorem fullRecordGapTerm06669_eq_value :
    recordGapCenter + 369752 = fullRecordGapValue06669 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06669_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06669 (fullRecordGapValue06669 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06669_not_prime : ¬(recordGapCenter + 369752).Prime := by
  rw [fullRecordGapTerm06669_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06669, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06669_fast_pow_mod_ne_one

def fullRecordGapValue06670 : Nat := fullRecordGapCenterValue + 369758

theorem fullRecordGapTerm06670_eq_value :
    recordGapCenter + 369758 = fullRecordGapValue06670 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06670_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06670 (fullRecordGapValue06670 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06670_not_prime : ¬(recordGapCenter + 369758).Prime := by
  rw [fullRecordGapTerm06670_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06670, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06670_fast_pow_mod_ne_one

def fullRecordGapValue06671 : Nat := fullRecordGapCenterValue + 369906

theorem fullRecordGapTerm06671_eq_value :
    recordGapCenter + 369906 = fullRecordGapValue06671 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06671_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06671 (fullRecordGapValue06671 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06671_not_prime : ¬(recordGapCenter + 369906).Prime := by
  rw [fullRecordGapTerm06671_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06671, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06671_fast_pow_mod_ne_one

def fullRecordGapValue06672 : Nat := fullRecordGapCenterValue + 369986

theorem fullRecordGapTerm06672_eq_value :
    recordGapCenter + 369986 = fullRecordGapValue06672 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06672_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06672 (fullRecordGapValue06672 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06672_not_prime : ¬(recordGapCenter + 369986).Prime := by
  rw [fullRecordGapTerm06672_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06672, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06672_fast_pow_mod_ne_one

def fullRecordGapValue06673 : Nat := fullRecordGapCenterValue + 370002

theorem fullRecordGapTerm06673_eq_value :
    recordGapCenter + 370002 = fullRecordGapValue06673 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06673_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06673 (fullRecordGapValue06673 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06673_not_prime : ¬(recordGapCenter + 370002).Prime := by
  rw [fullRecordGapTerm06673_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06673, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06673_fast_pow_mod_ne_one

def fullRecordGapValue06674 : Nat := fullRecordGapCenterValue + 370086

theorem fullRecordGapTerm06674_eq_value :
    recordGapCenter + 370086 = fullRecordGapValue06674 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06674_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06674 (fullRecordGapValue06674 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06674_not_prime : ¬(recordGapCenter + 370086).Prime := by
  rw [fullRecordGapTerm06674_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06674, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06674_fast_pow_mod_ne_one

def fullRecordGapValue06675 : Nat := fullRecordGapCenterValue + 370088

theorem fullRecordGapTerm06675_eq_value :
    recordGapCenter + 370088 = fullRecordGapValue06675 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06675_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06675 (fullRecordGapValue06675 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06675_not_prime : ¬(recordGapCenter + 370088).Prime := by
  rw [fullRecordGapTerm06675_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06675, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06675_fast_pow_mod_ne_one

def fullRecordGapValue06676 : Nat := fullRecordGapCenterValue + 370122

theorem fullRecordGapTerm06676_eq_value :
    recordGapCenter + 370122 = fullRecordGapValue06676 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06676_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06676 (fullRecordGapValue06676 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06676_not_prime : ¬(recordGapCenter + 370122).Prime := by
  rw [fullRecordGapTerm06676_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06676, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06676_fast_pow_mod_ne_one

def fullRecordGapValue06677 : Nat := fullRecordGapCenterValue + 370232

theorem fullRecordGapTerm06677_eq_value :
    recordGapCenter + 370232 = fullRecordGapValue06677 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06677_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06677 (fullRecordGapValue06677 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06677_not_prime : ¬(recordGapCenter + 370232).Prime := by
  rw [fullRecordGapTerm06677_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06677, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06677_fast_pow_mod_ne_one

def fullRecordGapValue06678 : Nat := fullRecordGapCenterValue + 370262

theorem fullRecordGapTerm06678_eq_value :
    recordGapCenter + 370262 = fullRecordGapValue06678 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06678_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06678 (fullRecordGapValue06678 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06678_not_prime : ¬(recordGapCenter + 370262).Prime := by
  rw [fullRecordGapTerm06678_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06678, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06678_fast_pow_mod_ne_one

def fullRecordGapValue06679 : Nat := fullRecordGapCenterValue + 370338

theorem fullRecordGapTerm06679_eq_value :
    recordGapCenter + 370338 = fullRecordGapValue06679 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06679_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06679 (fullRecordGapValue06679 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06679_not_prime : ¬(recordGapCenter + 370338).Prime := by
  rw [fullRecordGapTerm06679_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06679, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06679_fast_pow_mod_ne_one

def fullRecordGapValue06680 : Nat := fullRecordGapCenterValue + 370472

theorem fullRecordGapTerm06680_eq_value :
    recordGapCenter + 370472 = fullRecordGapValue06680 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06680_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06680 (fullRecordGapValue06680 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06680_not_prime : ¬(recordGapCenter + 370472).Prime := by
  rw [fullRecordGapTerm06680_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06680, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06680_fast_pow_mod_ne_one

def fullRecordGapValue06681 : Nat := fullRecordGapCenterValue + 370506

theorem fullRecordGapTerm06681_eq_value :
    recordGapCenter + 370506 = fullRecordGapValue06681 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06681_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06681 (fullRecordGapValue06681 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06681_not_prime : ¬(recordGapCenter + 370506).Prime := by
  rw [fullRecordGapTerm06681_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06681, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06681_fast_pow_mod_ne_one

def fullRecordGapValue06682 : Nat := fullRecordGapCenterValue + 370598

theorem fullRecordGapTerm06682_eq_value :
    recordGapCenter + 370598 = fullRecordGapValue06682 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06682_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06682 (fullRecordGapValue06682 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06682_not_prime : ¬(recordGapCenter + 370598).Prime := by
  rw [fullRecordGapTerm06682_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06682, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06682_fast_pow_mod_ne_one

def fullRecordGapValue06683 : Nat := fullRecordGapCenterValue + 370646

theorem fullRecordGapTerm06683_eq_value :
    recordGapCenter + 370646 = fullRecordGapValue06683 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06683_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06683 (fullRecordGapValue06683 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06683_not_prime : ¬(recordGapCenter + 370646).Prime := by
  rw [fullRecordGapTerm06683_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06683, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06683_fast_pow_mod_ne_one

def fullRecordGapValue06684 : Nat := fullRecordGapCenterValue + 370676

theorem fullRecordGapTerm06684_eq_value :
    recordGapCenter + 370676 = fullRecordGapValue06684 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06684_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06684 (fullRecordGapValue06684 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06684_not_prime : ¬(recordGapCenter + 370676).Prime := by
  rw [fullRecordGapTerm06684_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06684, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06684_fast_pow_mod_ne_one

def fullRecordGapValue06685 : Nat := fullRecordGapCenterValue + 370686

theorem fullRecordGapTerm06685_eq_value :
    recordGapCenter + 370686 = fullRecordGapValue06685 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06685_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06685 (fullRecordGapValue06685 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06685_not_prime : ¬(recordGapCenter + 370686).Prime := by
  rw [fullRecordGapTerm06685_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06685, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06685_fast_pow_mod_ne_one

def fullRecordGapValue06686 : Nat := fullRecordGapCenterValue + 370742

theorem fullRecordGapTerm06686_eq_value :
    recordGapCenter + 370742 = fullRecordGapValue06686 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06686_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06686 (fullRecordGapValue06686 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06686_not_prime : ¬(recordGapCenter + 370742).Prime := by
  rw [fullRecordGapTerm06686_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06686, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06686_fast_pow_mod_ne_one

def fullRecordGapValue06687 : Nat := fullRecordGapCenterValue + 370802

theorem fullRecordGapTerm06687_eq_value :
    recordGapCenter + 370802 = fullRecordGapValue06687 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06687_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06687 (fullRecordGapValue06687 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06687_not_prime : ¬(recordGapCenter + 370802).Prime := by
  rw [fullRecordGapTerm06687_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06687, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06687_fast_pow_mod_ne_one

def fullRecordGapValue06688 : Nat := fullRecordGapCenterValue + 370868

theorem fullRecordGapTerm06688_eq_value :
    recordGapCenter + 370868 = fullRecordGapValue06688 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06688_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06688 (fullRecordGapValue06688 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06688_not_prime : ¬(recordGapCenter + 370868).Prime := by
  rw [fullRecordGapTerm06688_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06688, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06688_fast_pow_mod_ne_one

def fullRecordGapValue06689 : Nat := fullRecordGapCenterValue + 370892

theorem fullRecordGapTerm06689_eq_value :
    recordGapCenter + 370892 = fullRecordGapValue06689 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06689_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06689 (fullRecordGapValue06689 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06689_not_prime : ¬(recordGapCenter + 370892).Prime := by
  rw [fullRecordGapTerm06689_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06689, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06689_fast_pow_mod_ne_one

def fullRecordGapValue06690 : Nat := fullRecordGapCenterValue + 371012

theorem fullRecordGapTerm06690_eq_value :
    recordGapCenter + 371012 = fullRecordGapValue06690 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06690_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06690 (fullRecordGapValue06690 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06690_not_prime : ¬(recordGapCenter + 371012).Prime := by
  rw [fullRecordGapTerm06690_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06690, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06690_fast_pow_mod_ne_one

def fullRecordGapValue06691 : Nat := fullRecordGapCenterValue + 371058

theorem fullRecordGapTerm06691_eq_value :
    recordGapCenter + 371058 = fullRecordGapValue06691 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06691_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06691 (fullRecordGapValue06691 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06691_not_prime : ¬(recordGapCenter + 371058).Prime := by
  rw [fullRecordGapTerm06691_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06691, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06691_fast_pow_mod_ne_one

def fullRecordGapValue06692 : Nat := fullRecordGapCenterValue + 371066

theorem fullRecordGapTerm06692_eq_value :
    recordGapCenter + 371066 = fullRecordGapValue06692 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06692_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06692 (fullRecordGapValue06692 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06692_not_prime : ¬(recordGapCenter + 371066).Prime := by
  rw [fullRecordGapTerm06692_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06692, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06692_fast_pow_mod_ne_one

def fullRecordGapValue06693 : Nat := fullRecordGapCenterValue + 371250

theorem fullRecordGapTerm06693_eq_value :
    recordGapCenter + 371250 = fullRecordGapValue06693 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06693_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06693 (fullRecordGapValue06693 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06693_not_prime : ¬(recordGapCenter + 371250).Prime := by
  rw [fullRecordGapTerm06693_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06693, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06693_fast_pow_mod_ne_one

def fullRecordGapValue06694 : Nat := fullRecordGapCenterValue + 371288

theorem fullRecordGapTerm06694_eq_value :
    recordGapCenter + 371288 = fullRecordGapValue06694 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06694_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06694 (fullRecordGapValue06694 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06694_not_prime : ¬(recordGapCenter + 371288).Prime := by
  rw [fullRecordGapTerm06694_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06694, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06694_fast_pow_mod_ne_one

def fullRecordGapValue06695 : Nat := fullRecordGapCenterValue + 371366

theorem fullRecordGapTerm06695_eq_value :
    recordGapCenter + 371366 = fullRecordGapValue06695 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06695_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06695 (fullRecordGapValue06695 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06695_not_prime : ¬(recordGapCenter + 371366).Prime := by
  rw [fullRecordGapTerm06695_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06695, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06695_fast_pow_mod_ne_one

def fullRecordGapValue06696 : Nat := fullRecordGapCenterValue + 371498

theorem fullRecordGapTerm06696_eq_value :
    recordGapCenter + 371498 = fullRecordGapValue06696 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06696_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06696 (fullRecordGapValue06696 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06696_not_prime : ¬(recordGapCenter + 371498).Prime := by
  rw [fullRecordGapTerm06696_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06696, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06696_fast_pow_mod_ne_one

def fullRecordGapValue06697 : Nat := fullRecordGapCenterValue + 371528

theorem fullRecordGapTerm06697_eq_value :
    recordGapCenter + 371528 = fullRecordGapValue06697 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06697_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06697 (fullRecordGapValue06697 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06697_not_prime : ¬(recordGapCenter + 371528).Prime := by
  rw [fullRecordGapTerm06697_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06697, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06697_fast_pow_mod_ne_one

def fullRecordGapValue06698 : Nat := fullRecordGapCenterValue + 371666

theorem fullRecordGapTerm06698_eq_value :
    recordGapCenter + 371666 = fullRecordGapValue06698 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06698_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06698 (fullRecordGapValue06698 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06698_not_prime : ¬(recordGapCenter + 371666).Prime := by
  rw [fullRecordGapTerm06698_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06698, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06698_fast_pow_mod_ne_one

def fullRecordGapValue06699 : Nat := fullRecordGapCenterValue + 371738

theorem fullRecordGapTerm06699_eq_value :
    recordGapCenter + 371738 = fullRecordGapValue06699 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06699_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06699 (fullRecordGapValue06699 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06699_not_prime : ¬(recordGapCenter + 371738).Prime := by
  rw [fullRecordGapTerm06699_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06699, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06699_fast_pow_mod_ne_one

def fullRecordGapValue06700 : Nat := fullRecordGapCenterValue + 371886

theorem fullRecordGapTerm06700_eq_value :
    recordGapCenter + 371886 = fullRecordGapValue06700 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06700_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06700 (fullRecordGapValue06700 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06700_not_prime : ¬(recordGapCenter + 371886).Prime := by
  rw [fullRecordGapTerm06700_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06700, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06700_fast_pow_mod_ne_one

def fullRecordGapValue06701 : Nat := fullRecordGapCenterValue + 371946

theorem fullRecordGapTerm06701_eq_value :
    recordGapCenter + 371946 = fullRecordGapValue06701 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06701_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06701 (fullRecordGapValue06701 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06701_not_prime : ¬(recordGapCenter + 371946).Prime := by
  rw [fullRecordGapTerm06701_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06701, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06701_fast_pow_mod_ne_one

def fullRecordGapValue06702 : Nat := fullRecordGapCenterValue + 372282

theorem fullRecordGapTerm06702_eq_value :
    recordGapCenter + 372282 = fullRecordGapValue06702 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06702_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06702 (fullRecordGapValue06702 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06702_not_prime : ¬(recordGapCenter + 372282).Prime := by
  rw [fullRecordGapTerm06702_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06702, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06702_fast_pow_mod_ne_one

def fullRecordGapValue06703 : Nat := fullRecordGapCenterValue + 372332

theorem fullRecordGapTerm06703_eq_value :
    recordGapCenter + 372332 = fullRecordGapValue06703 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06703_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06703 (fullRecordGapValue06703 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06703_not_prime : ¬(recordGapCenter + 372332).Prime := by
  rw [fullRecordGapTerm06703_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06703, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06703_fast_pow_mod_ne_one

def fullRecordGapValue06704 : Nat := fullRecordGapCenterValue + 372342

theorem fullRecordGapTerm06704_eq_value :
    recordGapCenter + 372342 = fullRecordGapValue06704 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06704_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06704 (fullRecordGapValue06704 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06704_not_prime : ¬(recordGapCenter + 372342).Prime := by
  rw [fullRecordGapTerm06704_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06704, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06704_fast_pow_mod_ne_one

def fullRecordGapValue06705 : Nat := fullRecordGapCenterValue + 372426

theorem fullRecordGapTerm06705_eq_value :
    recordGapCenter + 372426 = fullRecordGapValue06705 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06705_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06705 (fullRecordGapValue06705 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06705_not_prime : ¬(recordGapCenter + 372426).Prime := by
  rw [fullRecordGapTerm06705_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06705, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06705_fast_pow_mod_ne_one

def fullRecordGapValue06706 : Nat := fullRecordGapCenterValue + 372486

theorem fullRecordGapTerm06706_eq_value :
    recordGapCenter + 372486 = fullRecordGapValue06706 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06706_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06706 (fullRecordGapValue06706 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06706_not_prime : ¬(recordGapCenter + 372486).Prime := by
  rw [fullRecordGapTerm06706_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06706, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06706_fast_pow_mod_ne_one

def fullRecordGapValue06707 : Nat := fullRecordGapCenterValue + 372536

theorem fullRecordGapTerm06707_eq_value :
    recordGapCenter + 372536 = fullRecordGapValue06707 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06707_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06707 (fullRecordGapValue06707 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06707_not_prime : ¬(recordGapCenter + 372536).Prime := by
  rw [fullRecordGapTerm06707_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06707, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06707_fast_pow_mod_ne_one

def fullRecordGapValue06708 : Nat := fullRecordGapCenterValue + 372542

theorem fullRecordGapTerm06708_eq_value :
    recordGapCenter + 372542 = fullRecordGapValue06708 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06708_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06708 (fullRecordGapValue06708 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06708_not_prime : ¬(recordGapCenter + 372542).Prime := by
  rw [fullRecordGapTerm06708_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06708, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06708_fast_pow_mod_ne_one

def fullRecordGapValue06709 : Nat := fullRecordGapCenterValue + 372680

theorem fullRecordGapTerm06709_eq_value :
    recordGapCenter + 372680 = fullRecordGapValue06709 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06709_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06709 (fullRecordGapValue06709 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06709_not_prime : ¬(recordGapCenter + 372680).Prime := by
  rw [fullRecordGapTerm06709_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06709, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06709_fast_pow_mod_ne_one

def fullRecordGapValue06710 : Nat := fullRecordGapCenterValue + 372782

theorem fullRecordGapTerm06710_eq_value :
    recordGapCenter + 372782 = fullRecordGapValue06710 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06710_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06710 (fullRecordGapValue06710 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06710_not_prime : ¬(recordGapCenter + 372782).Prime := by
  rw [fullRecordGapTerm06710_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06710, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06710_fast_pow_mod_ne_one

def fullRecordGapValue06711 : Nat := fullRecordGapCenterValue + 372822

theorem fullRecordGapTerm06711_eq_value :
    recordGapCenter + 372822 = fullRecordGapValue06711 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06711_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06711 (fullRecordGapValue06711 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06711_not_prime : ¬(recordGapCenter + 372822).Prime := by
  rw [fullRecordGapTerm06711_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06711, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06711_fast_pow_mod_ne_one

def fullRecordGapValue06712 : Nat := fullRecordGapCenterValue + 372858

theorem fullRecordGapTerm06712_eq_value :
    recordGapCenter + 372858 = fullRecordGapValue06712 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06712_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06712 (fullRecordGapValue06712 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06712_not_prime : ¬(recordGapCenter + 372858).Prime := by
  rw [fullRecordGapTerm06712_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06712, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06712_fast_pow_mod_ne_one

def fullRecordGapValue06713 : Nat := fullRecordGapCenterValue + 372902

theorem fullRecordGapTerm06713_eq_value :
    recordGapCenter + 372902 = fullRecordGapValue06713 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06713_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06713 (fullRecordGapValue06713 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06713_not_prime : ¬(recordGapCenter + 372902).Prime := by
  rw [fullRecordGapTerm06713_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06713, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06713_fast_pow_mod_ne_one

def fullRecordGapValue06714 : Nat := fullRecordGapCenterValue + 372956

theorem fullRecordGapTerm06714_eq_value :
    recordGapCenter + 372956 = fullRecordGapValue06714 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06714_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06714 (fullRecordGapValue06714 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06714_not_prime : ¬(recordGapCenter + 372956).Prime := by
  rw [fullRecordGapTerm06714_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06714, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06714_fast_pow_mod_ne_one

def fullRecordGapValue06715 : Nat := fullRecordGapCenterValue + 373026

theorem fullRecordGapTerm06715_eq_value :
    recordGapCenter + 373026 = fullRecordGapValue06715 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06715_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06715 (fullRecordGapValue06715 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06715_not_prime : ¬(recordGapCenter + 373026).Prime := by
  rw [fullRecordGapTerm06715_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06715, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06715_fast_pow_mod_ne_one

def fullRecordGapValue06716 : Nat := fullRecordGapCenterValue + 373052

theorem fullRecordGapTerm06716_eq_value :
    recordGapCenter + 373052 = fullRecordGapValue06716 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06716_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06716 (fullRecordGapValue06716 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06716_not_prime : ¬(recordGapCenter + 373052).Prime := by
  rw [fullRecordGapTerm06716_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06716, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06716_fast_pow_mod_ne_one

def fullRecordGapValue06717 : Nat := fullRecordGapCenterValue + 373112

theorem fullRecordGapTerm06717_eq_value :
    recordGapCenter + 373112 = fullRecordGapValue06717 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06717_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06717 (fullRecordGapValue06717 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06717_not_prime : ¬(recordGapCenter + 373112).Prime := by
  rw [fullRecordGapTerm06717_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06717, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06717_fast_pow_mod_ne_one

def fullRecordGapValue06718 : Nat := fullRecordGapCenterValue + 373146

theorem fullRecordGapTerm06718_eq_value :
    recordGapCenter + 373146 = fullRecordGapValue06718 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06718_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06718 (fullRecordGapValue06718 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06718_not_prime : ¬(recordGapCenter + 373146).Prime := by
  rw [fullRecordGapTerm06718_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06718, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06718_fast_pow_mod_ne_one

def fullRecordGapValue06719 : Nat := fullRecordGapCenterValue + 373206

theorem fullRecordGapTerm06719_eq_value :
    recordGapCenter + 373206 = fullRecordGapValue06719 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06719_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06719 (fullRecordGapValue06719 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06719_not_prime : ¬(recordGapCenter + 373206).Prime := by
  rw [fullRecordGapTerm06719_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06719, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06719_fast_pow_mod_ne_one

def fullRecordGapValue06720 : Nat := fullRecordGapCenterValue + 373238

theorem fullRecordGapTerm06720_eq_value :
    recordGapCenter + 373238 = fullRecordGapValue06720 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06720_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06720 (fullRecordGapValue06720 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06720_not_prime : ¬(recordGapCenter + 373238).Prime := by
  rw [fullRecordGapTerm06720_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06720, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06720_fast_pow_mod_ne_one

def fullRecordGapValue06721 : Nat := fullRecordGapCenterValue + 373242

theorem fullRecordGapTerm06721_eq_value :
    recordGapCenter + 373242 = fullRecordGapValue06721 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06721_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06721 (fullRecordGapValue06721 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06721_not_prime : ¬(recordGapCenter + 373242).Prime := by
  rw [fullRecordGapTerm06721_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06721, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06721_fast_pow_mod_ne_one

def fullRecordGapValue06722 : Nat := fullRecordGapCenterValue + 373278

theorem fullRecordGapTerm06722_eq_value :
    recordGapCenter + 373278 = fullRecordGapValue06722 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06722_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06722 (fullRecordGapValue06722 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06722_not_prime : ¬(recordGapCenter + 373278).Prime := by
  rw [fullRecordGapTerm06722_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06722, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06722_fast_pow_mod_ne_one

def fullRecordGapValue06723 : Nat := fullRecordGapCenterValue + 373448

theorem fullRecordGapTerm06723_eq_value :
    recordGapCenter + 373448 = fullRecordGapValue06723 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06723_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06723 (fullRecordGapValue06723 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06723_not_prime : ¬(recordGapCenter + 373448).Prime := by
  rw [fullRecordGapTerm06723_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06723, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06723_fast_pow_mod_ne_one

def fullRecordGapValue06724 : Nat := fullRecordGapCenterValue + 373508

theorem fullRecordGapTerm06724_eq_value :
    recordGapCenter + 373508 = fullRecordGapValue06724 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06724_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06724 (fullRecordGapValue06724 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06724_not_prime : ¬(recordGapCenter + 373508).Prime := by
  rw [fullRecordGapTerm06724_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06724, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06724_fast_pow_mod_ne_one

def fullRecordGapValue06725 : Nat := fullRecordGapCenterValue + 373532

theorem fullRecordGapTerm06725_eq_value :
    recordGapCenter + 373532 = fullRecordGapValue06725 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06725_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06725 (fullRecordGapValue06725 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06725_not_prime : ¬(recordGapCenter + 373532).Prime := by
  rw [fullRecordGapTerm06725_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06725, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06725_fast_pow_mod_ne_one

def fullRecordGapValue06726 : Nat := fullRecordGapCenterValue + 373586

theorem fullRecordGapTerm06726_eq_value :
    recordGapCenter + 373586 = fullRecordGapValue06726 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06726_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06726 (fullRecordGapValue06726 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06726_not_prime : ¬(recordGapCenter + 373586).Prime := by
  rw [fullRecordGapTerm06726_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06726, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06726_fast_pow_mod_ne_one

def fullRecordGapValue06727 : Nat := fullRecordGapCenterValue + 373628

theorem fullRecordGapTerm06727_eq_value :
    recordGapCenter + 373628 = fullRecordGapValue06727 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06727_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06727 (fullRecordGapValue06727 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06727_not_prime : ¬(recordGapCenter + 373628).Prime := by
  rw [fullRecordGapTerm06727_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06727, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06727_fast_pow_mod_ne_one

def fullRecordGapValue06728 : Nat := fullRecordGapCenterValue + 373676

theorem fullRecordGapTerm06728_eq_value :
    recordGapCenter + 373676 = fullRecordGapValue06728 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06728_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06728 (fullRecordGapValue06728 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06728_not_prime : ¬(recordGapCenter + 373676).Prime := by
  rw [fullRecordGapTerm06728_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06728, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06728_fast_pow_mod_ne_one

def fullRecordGapValue06729 : Nat := fullRecordGapCenterValue + 373718

theorem fullRecordGapTerm06729_eq_value :
    recordGapCenter + 373718 = fullRecordGapValue06729 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06729_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06729 (fullRecordGapValue06729 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06729_not_prime : ¬(recordGapCenter + 373718).Prime := by
  rw [fullRecordGapTerm06729_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06729, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06729_fast_pow_mod_ne_one

def fullRecordGapValue06730 : Nat := fullRecordGapCenterValue + 373766

theorem fullRecordGapTerm06730_eq_value :
    recordGapCenter + 373766 = fullRecordGapValue06730 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06730_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06730 (fullRecordGapValue06730 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06730_not_prime : ¬(recordGapCenter + 373766).Prime := by
  rw [fullRecordGapTerm06730_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06730, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06730_fast_pow_mod_ne_one

def fullRecordGapValue06731 : Nat := fullRecordGapCenterValue + 373866

theorem fullRecordGapTerm06731_eq_value :
    recordGapCenter + 373866 = fullRecordGapValue06731 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06731_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06731 (fullRecordGapValue06731 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06731_not_prime : ¬(recordGapCenter + 373866).Prime := by
  rw [fullRecordGapTerm06731_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06731, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06731_fast_pow_mod_ne_one

def fullRecordGapValue06732 : Nat := fullRecordGapCenterValue + 373938

theorem fullRecordGapTerm06732_eq_value :
    recordGapCenter + 373938 = fullRecordGapValue06732 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06732_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06732 (fullRecordGapValue06732 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06732_not_prime : ¬(recordGapCenter + 373938).Prime := by
  rw [fullRecordGapTerm06732_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06732, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06732_fast_pow_mod_ne_one

def fullRecordGapValue06733 : Nat := fullRecordGapCenterValue + 373962

theorem fullRecordGapTerm06733_eq_value :
    recordGapCenter + 373962 = fullRecordGapValue06733 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06733_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06733 (fullRecordGapValue06733 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06733_not_prime : ¬(recordGapCenter + 373962).Prime := by
  rw [fullRecordGapTerm06733_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06733, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06733_fast_pow_mod_ne_one

def fullRecordGapValue06734 : Nat := fullRecordGapCenterValue + 374082

theorem fullRecordGapTerm06734_eq_value :
    recordGapCenter + 374082 = fullRecordGapValue06734 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06734_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06734 (fullRecordGapValue06734 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06734_not_prime : ¬(recordGapCenter + 374082).Prime := by
  rw [fullRecordGapTerm06734_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06734, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06734_fast_pow_mod_ne_one

def fullRecordGapValue06735 : Nat := fullRecordGapCenterValue + 374138

theorem fullRecordGapTerm06735_eq_value :
    recordGapCenter + 374138 = fullRecordGapValue06735 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06735_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06735 (fullRecordGapValue06735 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06735_not_prime : ¬(recordGapCenter + 374138).Prime := by
  rw [fullRecordGapTerm06735_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06735, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06735_fast_pow_mod_ne_one

def fullRecordGapValue06736 : Nat := fullRecordGapCenterValue + 374162

theorem fullRecordGapTerm06736_eq_value :
    recordGapCenter + 374162 = fullRecordGapValue06736 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06736_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06736 (fullRecordGapValue06736 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06736_not_prime : ¬(recordGapCenter + 374162).Prime := by
  rw [fullRecordGapTerm06736_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06736, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06736_fast_pow_mod_ne_one

def fullRecordGapValue06737 : Nat := fullRecordGapCenterValue + 374222

theorem fullRecordGapTerm06737_eq_value :
    recordGapCenter + 374222 = fullRecordGapValue06737 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06737_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06737 (fullRecordGapValue06737 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06737_not_prime : ¬(recordGapCenter + 374222).Prime := by
  rw [fullRecordGapTerm06737_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06737, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06737_fast_pow_mod_ne_one

def fullRecordGapValue06738 : Nat := fullRecordGapCenterValue + 374228

theorem fullRecordGapTerm06738_eq_value :
    recordGapCenter + 374228 = fullRecordGapValue06738 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06738_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06738 (fullRecordGapValue06738 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06738_not_prime : ¬(recordGapCenter + 374228).Prime := by
  rw [fullRecordGapTerm06738_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06738, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06738_fast_pow_mod_ne_one

def fullRecordGapValue06739 : Nat := fullRecordGapCenterValue + 374246

theorem fullRecordGapTerm06739_eq_value :
    recordGapCenter + 374246 = fullRecordGapValue06739 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06739_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06739 (fullRecordGapValue06739 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06739_not_prime : ¬(recordGapCenter + 374246).Prime := by
  rw [fullRecordGapTerm06739_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06739, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06739_fast_pow_mod_ne_one

def fullRecordGapValue06740 : Nat := fullRecordGapCenterValue + 374298

theorem fullRecordGapTerm06740_eq_value :
    recordGapCenter + 374298 = fullRecordGapValue06740 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06740_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06740 (fullRecordGapValue06740 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06740_not_prime : ¬(recordGapCenter + 374298).Prime := by
  rw [fullRecordGapTerm06740_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06740, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06740_fast_pow_mod_ne_one

def fullRecordGapValue06741 : Nat := fullRecordGapCenterValue + 374406

theorem fullRecordGapTerm06741_eq_value :
    recordGapCenter + 374406 = fullRecordGapValue06741 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06741_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06741 (fullRecordGapValue06741 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06741_not_prime : ¬(recordGapCenter + 374406).Prime := by
  rw [fullRecordGapTerm06741_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06741, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06741_fast_pow_mod_ne_one

def fullRecordGapValue06742 : Nat := fullRecordGapCenterValue + 374456

theorem fullRecordGapTerm06742_eq_value :
    recordGapCenter + 374456 = fullRecordGapValue06742 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06742_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06742 (fullRecordGapValue06742 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06742_not_prime : ¬(recordGapCenter + 374456).Prime := by
  rw [fullRecordGapTerm06742_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06742, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06742_fast_pow_mod_ne_one

def fullRecordGapValue06743 : Nat := fullRecordGapCenterValue + 374732

theorem fullRecordGapTerm06743_eq_value :
    recordGapCenter + 374732 = fullRecordGapValue06743 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06743_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06743 (fullRecordGapValue06743 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06743_not_prime : ¬(recordGapCenter + 374732).Prime := by
  rw [fullRecordGapTerm06743_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06743, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06743_fast_pow_mod_ne_one

def fullRecordGapValue06744 : Nat := fullRecordGapCenterValue + 374862

theorem fullRecordGapTerm06744_eq_value :
    recordGapCenter + 374862 = fullRecordGapValue06744 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06744_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06744 (fullRecordGapValue06744 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06744_not_prime : ¬(recordGapCenter + 374862).Prime := by
  rw [fullRecordGapTerm06744_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06744, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06744_fast_pow_mod_ne_one

def fullRecordGapValue06745 : Nat := fullRecordGapCenterValue + 374936

theorem fullRecordGapTerm06745_eq_value :
    recordGapCenter + 374936 = fullRecordGapValue06745 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06745_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06745 (fullRecordGapValue06745 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06745_not_prime : ¬(recordGapCenter + 374936).Prime := by
  rw [fullRecordGapTerm06745_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06745, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06745_fast_pow_mod_ne_one

def fullRecordGapValue06746 : Nat := fullRecordGapCenterValue + 375006

theorem fullRecordGapTerm06746_eq_value :
    recordGapCenter + 375006 = fullRecordGapValue06746 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06746_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06746 (fullRecordGapValue06746 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06746_not_prime : ¬(recordGapCenter + 375006).Prime := by
  rw [fullRecordGapTerm06746_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06746, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06746_fast_pow_mod_ne_one

def fullRecordGapValue06747 : Nat := fullRecordGapCenterValue + 375026

theorem fullRecordGapTerm06747_eq_value :
    recordGapCenter + 375026 = fullRecordGapValue06747 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06747_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06747 (fullRecordGapValue06747 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06747_not_prime : ¬(recordGapCenter + 375026).Prime := by
  rw [fullRecordGapTerm06747_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06747, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06747_fast_pow_mod_ne_one

def fullRecordGapValue06748 : Nat := fullRecordGapCenterValue + 375236

theorem fullRecordGapTerm06748_eq_value :
    recordGapCenter + 375236 = fullRecordGapValue06748 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06748_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06748 (fullRecordGapValue06748 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06748_not_prime : ¬(recordGapCenter + 375236).Prime := by
  rw [fullRecordGapTerm06748_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06748, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06748_fast_pow_mod_ne_one

def fullRecordGapValue06749 : Nat := fullRecordGapCenterValue + 375302

theorem fullRecordGapTerm06749_eq_value :
    recordGapCenter + 375302 = fullRecordGapValue06749 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06749_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06749 (fullRecordGapValue06749 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06749_not_prime : ¬(recordGapCenter + 375302).Prime := by
  rw [fullRecordGapTerm06749_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06749, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06749_fast_pow_mod_ne_one

def fullRecordGapValue06750 : Nat := fullRecordGapCenterValue + 375546

theorem fullRecordGapTerm06750_eq_value :
    recordGapCenter + 375546 = fullRecordGapValue06750 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06750_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06750 (fullRecordGapValue06750 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06750_not_prime : ¬(recordGapCenter + 375546).Prime := by
  rw [fullRecordGapTerm06750_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06750, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06750_fast_pow_mod_ne_one

def fullRecordGapValue06751 : Nat := fullRecordGapCenterValue + 375548

theorem fullRecordGapTerm06751_eq_value :
    recordGapCenter + 375548 = fullRecordGapValue06751 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06751_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06751 (fullRecordGapValue06751 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06751_not_prime : ¬(recordGapCenter + 375548).Prime := by
  rw [fullRecordGapTerm06751_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06751, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06751_fast_pow_mod_ne_one

def fullRecordGapValue06752 : Nat := fullRecordGapCenterValue + 375656

theorem fullRecordGapTerm06752_eq_value :
    recordGapCenter + 375656 = fullRecordGapValue06752 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06752_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06752 (fullRecordGapValue06752 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06752_not_prime : ¬(recordGapCenter + 375656).Prime := by
  rw [fullRecordGapTerm06752_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06752, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06752_fast_pow_mod_ne_one

def fullRecordGapValue06753 : Nat := fullRecordGapCenterValue + 375722

theorem fullRecordGapTerm06753_eq_value :
    recordGapCenter + 375722 = fullRecordGapValue06753 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06753_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06753 (fullRecordGapValue06753 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06753_not_prime : ¬(recordGapCenter + 375722).Prime := by
  rw [fullRecordGapTerm06753_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06753, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06753_fast_pow_mod_ne_one

def fullRecordGapValue06754 : Nat := fullRecordGapCenterValue + 375798

theorem fullRecordGapTerm06754_eq_value :
    recordGapCenter + 375798 = fullRecordGapValue06754 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06754_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06754 (fullRecordGapValue06754 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06754_not_prime : ¬(recordGapCenter + 375798).Prime := by
  rw [fullRecordGapTerm06754_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06754, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06754_fast_pow_mod_ne_one

def fullRecordGapValue06755 : Nat := fullRecordGapCenterValue + 375842

theorem fullRecordGapTerm06755_eq_value :
    recordGapCenter + 375842 = fullRecordGapValue06755 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06755_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06755 (fullRecordGapValue06755 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06755_not_prime : ¬(recordGapCenter + 375842).Prime := by
  rw [fullRecordGapTerm06755_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06755, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06755_fast_pow_mod_ne_one

def fullRecordGapValue06756 : Nat := fullRecordGapCenterValue + 375902

theorem fullRecordGapTerm06756_eq_value :
    recordGapCenter + 375902 = fullRecordGapValue06756 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06756_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06756 (fullRecordGapValue06756 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06756_not_prime : ¬(recordGapCenter + 375902).Prime := by
  rw [fullRecordGapTerm06756_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06756, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06756_fast_pow_mod_ne_one

def fullRecordGapValue06757 : Nat := fullRecordGapCenterValue + 376098

theorem fullRecordGapTerm06757_eq_value :
    recordGapCenter + 376098 = fullRecordGapValue06757 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06757_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06757 (fullRecordGapValue06757 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06757_not_prime : ¬(recordGapCenter + 376098).Prime := by
  rw [fullRecordGapTerm06757_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06757, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06757_fast_pow_mod_ne_one

def fullRecordGapValue06758 : Nat := fullRecordGapCenterValue + 376122

theorem fullRecordGapTerm06758_eq_value :
    recordGapCenter + 376122 = fullRecordGapValue06758 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06758_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06758 (fullRecordGapValue06758 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06758_not_prime : ¬(recordGapCenter + 376122).Prime := by
  rw [fullRecordGapTerm06758_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06758, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06758_fast_pow_mod_ne_one

def fullRecordGapValue06759 : Nat := fullRecordGapCenterValue + 376136

theorem fullRecordGapTerm06759_eq_value :
    recordGapCenter + 376136 = fullRecordGapValue06759 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06759_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06759 (fullRecordGapValue06759 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06759_not_prime : ¬(recordGapCenter + 376136).Prime := by
  rw [fullRecordGapTerm06759_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06759, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06759_fast_pow_mod_ne_one

def fullRecordGapValue06760 : Nat := fullRecordGapCenterValue + 376338

theorem fullRecordGapTerm06760_eq_value :
    recordGapCenter + 376338 = fullRecordGapValue06760 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06760_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06760 (fullRecordGapValue06760 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06760_not_prime : ¬(recordGapCenter + 376338).Prime := by
  rw [fullRecordGapTerm06760_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06760, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06760_fast_pow_mod_ne_one

def fullRecordGapValue06761 : Nat := fullRecordGapCenterValue + 376358

theorem fullRecordGapTerm06761_eq_value :
    recordGapCenter + 376358 = fullRecordGapValue06761 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06761_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06761 (fullRecordGapValue06761 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06761_not_prime : ¬(recordGapCenter + 376358).Prime := by
  rw [fullRecordGapTerm06761_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06761, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06761_fast_pow_mod_ne_one

def fullRecordGapValue06762 : Nat := fullRecordGapCenterValue + 376386

theorem fullRecordGapTerm06762_eq_value :
    recordGapCenter + 376386 = fullRecordGapValue06762 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06762_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06762 (fullRecordGapValue06762 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06762_not_prime : ¬(recordGapCenter + 376386).Prime := by
  rw [fullRecordGapTerm06762_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06762, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06762_fast_pow_mod_ne_one

def fullRecordGapValue06763 : Nat := fullRecordGapCenterValue + 376458

theorem fullRecordGapTerm06763_eq_value :
    recordGapCenter + 376458 = fullRecordGapValue06763 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06763_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06763 (fullRecordGapValue06763 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06763_not_prime : ¬(recordGapCenter + 376458).Prime := by
  rw [fullRecordGapTerm06763_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06763, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06763_fast_pow_mod_ne_one

def fullRecordGapValue06764 : Nat := fullRecordGapCenterValue + 376472

theorem fullRecordGapTerm06764_eq_value :
    recordGapCenter + 376472 = fullRecordGapValue06764 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06764_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06764 (fullRecordGapValue06764 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06764_not_prime : ¬(recordGapCenter + 376472).Prime := by
  rw [fullRecordGapTerm06764_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06764, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06764_fast_pow_mod_ne_one

def fullRecordGapValue06765 : Nat := fullRecordGapCenterValue + 376518

theorem fullRecordGapTerm06765_eq_value :
    recordGapCenter + 376518 = fullRecordGapValue06765 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06765_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06765 (fullRecordGapValue06765 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06765_not_prime : ¬(recordGapCenter + 376518).Prime := by
  rw [fullRecordGapTerm06765_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06765, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06765_fast_pow_mod_ne_one

def fullRecordGapValue06766 : Nat := fullRecordGapCenterValue + 376622

theorem fullRecordGapTerm06766_eq_value :
    recordGapCenter + 376622 = fullRecordGapValue06766 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06766_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06766 (fullRecordGapValue06766 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06766_not_prime : ¬(recordGapCenter + 376622).Prime := by
  rw [fullRecordGapTerm06766_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06766, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06766_fast_pow_mod_ne_one

def fullRecordGapValue06767 : Nat := fullRecordGapCenterValue + 376638

theorem fullRecordGapTerm06767_eq_value :
    recordGapCenter + 376638 = fullRecordGapValue06767 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06767_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06767 (fullRecordGapValue06767 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06767_not_prime : ¬(recordGapCenter + 376638).Prime := by
  rw [fullRecordGapTerm06767_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06767, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06767_fast_pow_mod_ne_one

def fullRecordGapValue06768 : Nat := fullRecordGapCenterValue + 376646

theorem fullRecordGapTerm06768_eq_value :
    recordGapCenter + 376646 = fullRecordGapValue06768 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06768_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06768 (fullRecordGapValue06768 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06768_not_prime : ¬(recordGapCenter + 376646).Prime := by
  rw [fullRecordGapTerm06768_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06768, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06768_fast_pow_mod_ne_one

def fullRecordGapValue06769 : Nat := fullRecordGapCenterValue + 376806

theorem fullRecordGapTerm06769_eq_value :
    recordGapCenter + 376806 = fullRecordGapValue06769 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06769_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06769 (fullRecordGapValue06769 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06769_not_prime : ¬(recordGapCenter + 376806).Prime := by
  rw [fullRecordGapTerm06769_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06769, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06769_fast_pow_mod_ne_one

def fullRecordGapValue06770 : Nat := fullRecordGapCenterValue + 376862

theorem fullRecordGapTerm06770_eq_value :
    recordGapCenter + 376862 = fullRecordGapValue06770 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06770_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06770 (fullRecordGapValue06770 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06770_not_prime : ¬(recordGapCenter + 376862).Prime := by
  rw [fullRecordGapTerm06770_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06770, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06770_fast_pow_mod_ne_one

def fullRecordGapValue06771 : Nat := fullRecordGapCenterValue + 377066

theorem fullRecordGapTerm06771_eq_value :
    recordGapCenter + 377066 = fullRecordGapValue06771 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06771_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06771 (fullRecordGapValue06771 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06771_not_prime : ¬(recordGapCenter + 377066).Prime := by
  rw [fullRecordGapTerm06771_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06771, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06771_fast_pow_mod_ne_one

def fullRecordGapValue06772 : Nat := fullRecordGapCenterValue + 377106

theorem fullRecordGapTerm06772_eq_value :
    recordGapCenter + 377106 = fullRecordGapValue06772 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06772_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06772 (fullRecordGapValue06772 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06772_not_prime : ¬(recordGapCenter + 377106).Prime := by
  rw [fullRecordGapTerm06772_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06772, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06772_fast_pow_mod_ne_one

def fullRecordGapValue06773 : Nat := fullRecordGapCenterValue + 377300

theorem fullRecordGapTerm06773_eq_value :
    recordGapCenter + 377300 = fullRecordGapValue06773 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06773_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06773 (fullRecordGapValue06773 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06773_not_prime : ¬(recordGapCenter + 377300).Prime := by
  rw [fullRecordGapTerm06773_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06773, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06773_fast_pow_mod_ne_one

def fullRecordGapValue06774 : Nat := fullRecordGapCenterValue + 377372

theorem fullRecordGapTerm06774_eq_value :
    recordGapCenter + 377372 = fullRecordGapValue06774 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06774_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06774 (fullRecordGapValue06774 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06774_not_prime : ¬(recordGapCenter + 377372).Prime := by
  rw [fullRecordGapTerm06774_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06774, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06774_fast_pow_mod_ne_one

def fullRecordGapValue06775 : Nat := fullRecordGapCenterValue + 377382

theorem fullRecordGapTerm06775_eq_value :
    recordGapCenter + 377382 = fullRecordGapValue06775 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06775_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06775 (fullRecordGapValue06775 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06775_not_prime : ¬(recordGapCenter + 377382).Prime := by
  rw [fullRecordGapTerm06775_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06775, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06775_fast_pow_mod_ne_one

def fullRecordGapValue06776 : Nat := fullRecordGapCenterValue + 377402

theorem fullRecordGapTerm06776_eq_value :
    recordGapCenter + 377402 = fullRecordGapValue06776 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06776_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06776 (fullRecordGapValue06776 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06776_not_prime : ¬(recordGapCenter + 377402).Prime := by
  rw [fullRecordGapTerm06776_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06776, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06776_fast_pow_mod_ne_one

def fullRecordGapValue06777 : Nat := fullRecordGapCenterValue + 377438

theorem fullRecordGapTerm06777_eq_value :
    recordGapCenter + 377438 = fullRecordGapValue06777 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06777_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06777 (fullRecordGapValue06777 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06777_not_prime : ¬(recordGapCenter + 377438).Prime := by
  rw [fullRecordGapTerm06777_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06777, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06777_fast_pow_mod_ne_one

def fullRecordGapValue06778 : Nat := fullRecordGapCenterValue + 377588

theorem fullRecordGapTerm06778_eq_value :
    recordGapCenter + 377588 = fullRecordGapValue06778 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06778_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06778 (fullRecordGapValue06778 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06778_not_prime : ¬(recordGapCenter + 377588).Prime := by
  rw [fullRecordGapTerm06778_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06778, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06778_fast_pow_mod_ne_one

def fullRecordGapValue06779 : Nat := fullRecordGapCenterValue + 377708

theorem fullRecordGapTerm06779_eq_value :
    recordGapCenter + 377708 = fullRecordGapValue06779 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06779_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06779 (fullRecordGapValue06779 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06779_not_prime : ¬(recordGapCenter + 377708).Prime := by
  rw [fullRecordGapTerm06779_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06779, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06779_fast_pow_mod_ne_one

def fullRecordGapValue06780 : Nat := fullRecordGapCenterValue + 377738

theorem fullRecordGapTerm06780_eq_value :
    recordGapCenter + 377738 = fullRecordGapValue06780 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06780_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06780 (fullRecordGapValue06780 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06780_not_prime : ¬(recordGapCenter + 377738).Prime := by
  rw [fullRecordGapTerm06780_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06780, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06780_fast_pow_mod_ne_one

def fullRecordGapValue06781 : Nat := fullRecordGapCenterValue + 377756

theorem fullRecordGapTerm06781_eq_value :
    recordGapCenter + 377756 = fullRecordGapValue06781 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06781_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06781 (fullRecordGapValue06781 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06781_not_prime : ¬(recordGapCenter + 377756).Prime := by
  rw [fullRecordGapTerm06781_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06781, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06781_fast_pow_mod_ne_one

def fullRecordGapValue06782 : Nat := fullRecordGapCenterValue + 377822

theorem fullRecordGapTerm06782_eq_value :
    recordGapCenter + 377822 = fullRecordGapValue06782 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06782_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06782 (fullRecordGapValue06782 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06782_not_prime : ¬(recordGapCenter + 377822).Prime := by
  rw [fullRecordGapTerm06782_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06782, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06782_fast_pow_mod_ne_one

def fullRecordGapValue06783 : Nat := fullRecordGapCenterValue + 377826

theorem fullRecordGapTerm06783_eq_value :
    recordGapCenter + 377826 = fullRecordGapValue06783 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06783_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06783 (fullRecordGapValue06783 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06783_not_prime : ¬(recordGapCenter + 377826).Prime := by
  rw [fullRecordGapTerm06783_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06783, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06783_fast_pow_mod_ne_one

def fullRecordGapValue06784 : Nat := fullRecordGapCenterValue + 377898

theorem fullRecordGapTerm06784_eq_value :
    recordGapCenter + 377898 = fullRecordGapValue06784 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06784_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06784 (fullRecordGapValue06784 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06784_not_prime : ¬(recordGapCenter + 377898).Prime := by
  rw [fullRecordGapTerm06784_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06784, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06784_fast_pow_mod_ne_one

def fullRecordGapValue06785 : Nat := fullRecordGapCenterValue + 377906

theorem fullRecordGapTerm06785_eq_value :
    recordGapCenter + 377906 = fullRecordGapValue06785 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06785_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06785 (fullRecordGapValue06785 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06785_not_prime : ¬(recordGapCenter + 377906).Prime := by
  rw [fullRecordGapTerm06785_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06785, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06785_fast_pow_mod_ne_one

def fullRecordGapValue06786 : Nat := fullRecordGapCenterValue + 377966

theorem fullRecordGapTerm06786_eq_value :
    recordGapCenter + 377966 = fullRecordGapValue06786 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06786_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06786 (fullRecordGapValue06786 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06786_not_prime : ¬(recordGapCenter + 377966).Prime := by
  rw [fullRecordGapTerm06786_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06786, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06786_fast_pow_mod_ne_one

def fullRecordGapValue06787 : Nat := fullRecordGapCenterValue + 378008

theorem fullRecordGapTerm06787_eq_value :
    recordGapCenter + 378008 = fullRecordGapValue06787 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06787_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06787 (fullRecordGapValue06787 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06787_not_prime : ¬(recordGapCenter + 378008).Prime := by
  rw [fullRecordGapTerm06787_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06787, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06787_fast_pow_mod_ne_one

def fullRecordGapValue06788 : Nat := fullRecordGapCenterValue + 378038

theorem fullRecordGapTerm06788_eq_value :
    recordGapCenter + 378038 = fullRecordGapValue06788 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06788_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06788 (fullRecordGapValue06788 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06788_not_prime : ¬(recordGapCenter + 378038).Prime := by
  rw [fullRecordGapTerm06788_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06788, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06788_fast_pow_mod_ne_one

def fullRecordGapValue06789 : Nat := fullRecordGapCenterValue + 378086

theorem fullRecordGapTerm06789_eq_value :
    recordGapCenter + 378086 = fullRecordGapValue06789 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06789_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06789 (fullRecordGapValue06789 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06789_not_prime : ¬(recordGapCenter + 378086).Prime := by
  rw [fullRecordGapTerm06789_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06789, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06789_fast_pow_mod_ne_one

def fullRecordGapValue06790 : Nat := fullRecordGapCenterValue + 378278

theorem fullRecordGapTerm06790_eq_value :
    recordGapCenter + 378278 = fullRecordGapValue06790 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06790_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06790 (fullRecordGapValue06790 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06790_not_prime : ¬(recordGapCenter + 378278).Prime := by
  rw [fullRecordGapTerm06790_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06790, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06790_fast_pow_mod_ne_one

def fullRecordGapValue06791 : Nat := fullRecordGapCenterValue + 378296

theorem fullRecordGapTerm06791_eq_value :
    recordGapCenter + 378296 = fullRecordGapValue06791 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06791_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06791 (fullRecordGapValue06791 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06791_not_prime : ¬(recordGapCenter + 378296).Prime := by
  rw [fullRecordGapTerm06791_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06791, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06791_fast_pow_mod_ne_one

def fullRecordGapValue06792 : Nat := fullRecordGapCenterValue + 378402

theorem fullRecordGapTerm06792_eq_value :
    recordGapCenter + 378402 = fullRecordGapValue06792 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06792_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06792 (fullRecordGapValue06792 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06792_not_prime : ¬(recordGapCenter + 378402).Prime := by
  rw [fullRecordGapTerm06792_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06792, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06792_fast_pow_mod_ne_one

def fullRecordGapValue06793 : Nat := fullRecordGapCenterValue + 378438

theorem fullRecordGapTerm06793_eq_value :
    recordGapCenter + 378438 = fullRecordGapValue06793 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06793_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06793 (fullRecordGapValue06793 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06793_not_prime : ¬(recordGapCenter + 378438).Prime := by
  rw [fullRecordGapTerm06793_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06793, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06793_fast_pow_mod_ne_one

def fullRecordGapValue06794 : Nat := fullRecordGapCenterValue + 378458

theorem fullRecordGapTerm06794_eq_value :
    recordGapCenter + 378458 = fullRecordGapValue06794 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06794_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06794 (fullRecordGapValue06794 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06794_not_prime : ¬(recordGapCenter + 378458).Prime := by
  rw [fullRecordGapTerm06794_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06794, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06794_fast_pow_mod_ne_one

def fullRecordGapValue06795 : Nat := fullRecordGapCenterValue + 378536

theorem fullRecordGapTerm06795_eq_value :
    recordGapCenter + 378536 = fullRecordGapValue06795 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06795_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06795 (fullRecordGapValue06795 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06795_not_prime : ¬(recordGapCenter + 378536).Prime := by
  rw [fullRecordGapTerm06795_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06795, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06795_fast_pow_mod_ne_one

def fullRecordGapValue06796 : Nat := fullRecordGapCenterValue + 378542

theorem fullRecordGapTerm06796_eq_value :
    recordGapCenter + 378542 = fullRecordGapValue06796 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06796_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06796 (fullRecordGapValue06796 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06796_not_prime : ¬(recordGapCenter + 378542).Prime := by
  rw [fullRecordGapTerm06796_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06796, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06796_fast_pow_mod_ne_one

def fullRecordGapValue06797 : Nat := fullRecordGapCenterValue + 378582

theorem fullRecordGapTerm06797_eq_value :
    recordGapCenter + 378582 = fullRecordGapValue06797 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06797_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06797 (fullRecordGapValue06797 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06797_not_prime : ¬(recordGapCenter + 378582).Prime := by
  rw [fullRecordGapTerm06797_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06797, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06797_fast_pow_mod_ne_one

def fullRecordGapValue06798 : Nat := fullRecordGapCenterValue + 378722

theorem fullRecordGapTerm06798_eq_value :
    recordGapCenter + 378722 = fullRecordGapValue06798 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06798_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06798 (fullRecordGapValue06798 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06798_not_prime : ¬(recordGapCenter + 378722).Prime := by
  rw [fullRecordGapTerm06798_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06798, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06798_fast_pow_mod_ne_one

def fullRecordGapValue06799 : Nat := fullRecordGapCenterValue + 378786

theorem fullRecordGapTerm06799_eq_value :
    recordGapCenter + 378786 = fullRecordGapValue06799 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06799_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06799 (fullRecordGapValue06799 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06799_not_prime : ¬(recordGapCenter + 378786).Prime := by
  rw [fullRecordGapTerm06799_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06799, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06799_fast_pow_mod_ne_one

def fullRecordGapValue06800 : Nat := fullRecordGapCenterValue + 378866

theorem fullRecordGapTerm06800_eq_value :
    recordGapCenter + 378866 = fullRecordGapValue06800 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06800_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06800 (fullRecordGapValue06800 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06800_not_prime : ¬(recordGapCenter + 378866).Prime := by
  rw [fullRecordGapTerm06800_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06800, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06800_fast_pow_mod_ne_one

def fullRecordGapValue06801 : Nat := fullRecordGapCenterValue + 378878

theorem fullRecordGapTerm06801_eq_value :
    recordGapCenter + 378878 = fullRecordGapValue06801 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06801_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06801 (fullRecordGapValue06801 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06801_not_prime : ¬(recordGapCenter + 378878).Prime := by
  rw [fullRecordGapTerm06801_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06801, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06801_fast_pow_mod_ne_one

def fullRecordGapValue06802 : Nat := fullRecordGapCenterValue + 378908

theorem fullRecordGapTerm06802_eq_value :
    recordGapCenter + 378908 = fullRecordGapValue06802 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06802_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06802 (fullRecordGapValue06802 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06802_not_prime : ¬(recordGapCenter + 378908).Prime := by
  rw [fullRecordGapTerm06802_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06802, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06802_fast_pow_mod_ne_one

def fullRecordGapValue06803 : Nat := fullRecordGapCenterValue + 378926

theorem fullRecordGapTerm06803_eq_value :
    recordGapCenter + 378926 = fullRecordGapValue06803 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06803_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06803 (fullRecordGapValue06803 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06803_not_prime : ¬(recordGapCenter + 378926).Prime := by
  rw [fullRecordGapTerm06803_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06803, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06803_fast_pow_mod_ne_one

def fullRecordGapValue06804 : Nat := fullRecordGapCenterValue + 379058

theorem fullRecordGapTerm06804_eq_value :
    recordGapCenter + 379058 = fullRecordGapValue06804 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06804_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06804 (fullRecordGapValue06804 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06804_not_prime : ¬(recordGapCenter + 379058).Prime := by
  rw [fullRecordGapTerm06804_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06804, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06804_fast_pow_mod_ne_one

def fullRecordGapValue06805 : Nat := fullRecordGapCenterValue + 379172

theorem fullRecordGapTerm06805_eq_value :
    recordGapCenter + 379172 = fullRecordGapValue06805 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06805_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06805 (fullRecordGapValue06805 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06805_not_prime : ¬(recordGapCenter + 379172).Prime := by
  rw [fullRecordGapTerm06805_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06805, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06805_fast_pow_mod_ne_one

def fullRecordGapValue06806 : Nat := fullRecordGapCenterValue + 379292

theorem fullRecordGapTerm06806_eq_value :
    recordGapCenter + 379292 = fullRecordGapValue06806 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06806_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06806 (fullRecordGapValue06806 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06806_not_prime : ¬(recordGapCenter + 379292).Prime := by
  rw [fullRecordGapTerm06806_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06806, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06806_fast_pow_mod_ne_one

def fullRecordGapValue06807 : Nat := fullRecordGapCenterValue + 379352

theorem fullRecordGapTerm06807_eq_value :
    recordGapCenter + 379352 = fullRecordGapValue06807 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06807_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06807 (fullRecordGapValue06807 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06807_not_prime : ¬(recordGapCenter + 379352).Prime := by
  rw [fullRecordGapTerm06807_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06807, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06807_fast_pow_mod_ne_one

def fullRecordGapValue06808 : Nat := fullRecordGapCenterValue + 379388

theorem fullRecordGapTerm06808_eq_value :
    recordGapCenter + 379388 = fullRecordGapValue06808 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06808_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06808 (fullRecordGapValue06808 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06808_not_prime : ¬(recordGapCenter + 379388).Prime := by
  rw [fullRecordGapTerm06808_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06808, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06808_fast_pow_mod_ne_one

def fullRecordGapValue06809 : Nat := fullRecordGapCenterValue + 379446

theorem fullRecordGapTerm06809_eq_value :
    recordGapCenter + 379446 = fullRecordGapValue06809 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06809_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06809 (fullRecordGapValue06809 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06809_not_prime : ¬(recordGapCenter + 379446).Prime := by
  rw [fullRecordGapTerm06809_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06809, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06809_fast_pow_mod_ne_one

def fullRecordGapValue06810 : Nat := fullRecordGapCenterValue + 379466

theorem fullRecordGapTerm06810_eq_value :
    recordGapCenter + 379466 = fullRecordGapValue06810 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06810_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06810 (fullRecordGapValue06810 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06810_not_prime : ¬(recordGapCenter + 379466).Prime := by
  rw [fullRecordGapTerm06810_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06810, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06810_fast_pow_mod_ne_one

def fullRecordGapValue06811 : Nat := fullRecordGapCenterValue + 379598

theorem fullRecordGapTerm06811_eq_value :
    recordGapCenter + 379598 = fullRecordGapValue06811 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06811_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06811 (fullRecordGapValue06811 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06811_not_prime : ¬(recordGapCenter + 379598).Prime := by
  rw [fullRecordGapTerm06811_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06811, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06811_fast_pow_mod_ne_one

def fullRecordGapValue06812 : Nat := fullRecordGapCenterValue + 379646

theorem fullRecordGapTerm06812_eq_value :
    recordGapCenter + 379646 = fullRecordGapValue06812 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06812_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06812 (fullRecordGapValue06812 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06812_not_prime : ¬(recordGapCenter + 379646).Prime := by
  rw [fullRecordGapTerm06812_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06812, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06812_fast_pow_mod_ne_one

def fullRecordGapValue06813 : Nat := fullRecordGapCenterValue + 379718

theorem fullRecordGapTerm06813_eq_value :
    recordGapCenter + 379718 = fullRecordGapValue06813 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06813_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06813 (fullRecordGapValue06813 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06813_not_prime : ¬(recordGapCenter + 379718).Prime := by
  rw [fullRecordGapTerm06813_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06813, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06813_fast_pow_mod_ne_one

def fullRecordGapValue06814 : Nat := fullRecordGapCenterValue + 379878

theorem fullRecordGapTerm06814_eq_value :
    recordGapCenter + 379878 = fullRecordGapValue06814 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06814_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06814 (fullRecordGapValue06814 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06814_not_prime : ¬(recordGapCenter + 379878).Prime := by
  rw [fullRecordGapTerm06814_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06814, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06814_fast_pow_mod_ne_one

def fullRecordGapValue06815 : Nat := fullRecordGapCenterValue + 379902

theorem fullRecordGapTerm06815_eq_value :
    recordGapCenter + 379902 = fullRecordGapValue06815 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06815_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06815 (fullRecordGapValue06815 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06815_not_prime : ¬(recordGapCenter + 379902).Prime := by
  rw [fullRecordGapTerm06815_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06815, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06815_fast_pow_mod_ne_one

def fullRecordGapValue06816 : Nat := fullRecordGapCenterValue + 379928

theorem fullRecordGapTerm06816_eq_value :
    recordGapCenter + 379928 = fullRecordGapValue06816 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06816_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06816 (fullRecordGapValue06816 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06816_not_prime : ¬(recordGapCenter + 379928).Prime := by
  rw [fullRecordGapTerm06816_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06816, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06816_fast_pow_mod_ne_one

def fullRecordGapValue06817 : Nat := fullRecordGapCenterValue + 380012

theorem fullRecordGapTerm06817_eq_value :
    recordGapCenter + 380012 = fullRecordGapValue06817 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06817_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06817 (fullRecordGapValue06817 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06817_not_prime : ¬(recordGapCenter + 380012).Prime := by
  rw [fullRecordGapTerm06817_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06817, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06817_fast_pow_mod_ne_one

def fullRecordGapValue06818 : Nat := fullRecordGapCenterValue + 380126

theorem fullRecordGapTerm06818_eq_value :
    recordGapCenter + 380126 = fullRecordGapValue06818 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06818_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06818 (fullRecordGapValue06818 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06818_not_prime : ¬(recordGapCenter + 380126).Prime := by
  rw [fullRecordGapTerm06818_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06818, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06818_fast_pow_mod_ne_one

def fullRecordGapValue06819 : Nat := fullRecordGapCenterValue + 380168

theorem fullRecordGapTerm06819_eq_value :
    recordGapCenter + 380168 = fullRecordGapValue06819 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06819_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06819 (fullRecordGapValue06819 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06819_not_prime : ¬(recordGapCenter + 380168).Prime := by
  rw [fullRecordGapTerm06819_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06819, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06819_fast_pow_mod_ne_one

def fullRecordGapValue06820 : Nat := fullRecordGapCenterValue + 380186

theorem fullRecordGapTerm06820_eq_value :
    recordGapCenter + 380186 = fullRecordGapValue06820 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06820_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06820 (fullRecordGapValue06820 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06820_not_prime : ¬(recordGapCenter + 380186).Prime := by
  rw [fullRecordGapTerm06820_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06820, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06820_fast_pow_mod_ne_one

def fullRecordGapValue06821 : Nat := fullRecordGapCenterValue + 380252

theorem fullRecordGapTerm06821_eq_value :
    recordGapCenter + 380252 = fullRecordGapValue06821 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06821_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06821 (fullRecordGapValue06821 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06821_not_prime : ¬(recordGapCenter + 380252).Prime := by
  rw [fullRecordGapTerm06821_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06821, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06821_fast_pow_mod_ne_one

def fullRecordGapValue06822 : Nat := fullRecordGapCenterValue + 380258

theorem fullRecordGapTerm06822_eq_value :
    recordGapCenter + 380258 = fullRecordGapValue06822 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06822_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06822 (fullRecordGapValue06822 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06822_not_prime : ¬(recordGapCenter + 380258).Prime := by
  rw [fullRecordGapTerm06822_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06822, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06822_fast_pow_mod_ne_one

def fullRecordGapValue06823 : Nat := fullRecordGapCenterValue + 380348

theorem fullRecordGapTerm06823_eq_value :
    recordGapCenter + 380348 = fullRecordGapValue06823 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06823_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06823 (fullRecordGapValue06823 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06823_not_prime : ¬(recordGapCenter + 380348).Prime := by
  rw [fullRecordGapTerm06823_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06823, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06823_fast_pow_mod_ne_one

def fullRecordGapValue06824 : Nat := fullRecordGapCenterValue + 380642

theorem fullRecordGapTerm06824_eq_value :
    recordGapCenter + 380642 = fullRecordGapValue06824 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06824_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06824 (fullRecordGapValue06824 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06824_not_prime : ¬(recordGapCenter + 380642).Prime := by
  rw [fullRecordGapTerm06824_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06824, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06824_fast_pow_mod_ne_one

def fullRecordGapValue06825 : Nat := fullRecordGapCenterValue + 380648

theorem fullRecordGapTerm06825_eq_value :
    recordGapCenter + 380648 = fullRecordGapValue06825 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06825_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06825 (fullRecordGapValue06825 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06825_not_prime : ¬(recordGapCenter + 380648).Prime := by
  rw [fullRecordGapTerm06825_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06825, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06825_fast_pow_mod_ne_one

def fullRecordGapValue06826 : Nat := fullRecordGapCenterValue + 380852

theorem fullRecordGapTerm06826_eq_value :
    recordGapCenter + 380852 = fullRecordGapValue06826 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06826_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06826 (fullRecordGapValue06826 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06826_not_prime : ¬(recordGapCenter + 380852).Prime := by
  rw [fullRecordGapTerm06826_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06826, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06826_fast_pow_mod_ne_one

def fullRecordGapValue06827 : Nat := fullRecordGapCenterValue + 380958

theorem fullRecordGapTerm06827_eq_value :
    recordGapCenter + 380958 = fullRecordGapValue06827 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06827_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06827 (fullRecordGapValue06827 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06827_not_prime : ¬(recordGapCenter + 380958).Prime := by
  rw [fullRecordGapTerm06827_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06827, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06827_fast_pow_mod_ne_one

def fullRecordGapValue06828 : Nat := fullRecordGapCenterValue + 381032

theorem fullRecordGapTerm06828_eq_value :
    recordGapCenter + 381032 = fullRecordGapValue06828 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06828_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06828 (fullRecordGapValue06828 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06828_not_prime : ¬(recordGapCenter + 381032).Prime := by
  rw [fullRecordGapTerm06828_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06828, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06828_fast_pow_mod_ne_one

def fullRecordGapValue06829 : Nat := fullRecordGapCenterValue + 381068

theorem fullRecordGapTerm06829_eq_value :
    recordGapCenter + 381068 = fullRecordGapValue06829 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06829_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06829 (fullRecordGapValue06829 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06829_not_prime : ¬(recordGapCenter + 381068).Prime := by
  rw [fullRecordGapTerm06829_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06829, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06829_fast_pow_mod_ne_one

def fullRecordGapValue06830 : Nat := fullRecordGapCenterValue + 381126

theorem fullRecordGapTerm06830_eq_value :
    recordGapCenter + 381126 = fullRecordGapValue06830 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06830_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06830 (fullRecordGapValue06830 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06830_not_prime : ¬(recordGapCenter + 381126).Prime := by
  rw [fullRecordGapTerm06830_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06830, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06830_fast_pow_mod_ne_one

def fullRecordGapValue06831 : Nat := fullRecordGapCenterValue + 381246

theorem fullRecordGapTerm06831_eq_value :
    recordGapCenter + 381246 = fullRecordGapValue06831 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06831_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06831 (fullRecordGapValue06831 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06831_not_prime : ¬(recordGapCenter + 381246).Prime := by
  rw [fullRecordGapTerm06831_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06831, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06831_fast_pow_mod_ne_one

def fullRecordGapValue06832 : Nat := fullRecordGapCenterValue + 381272

theorem fullRecordGapTerm06832_eq_value :
    recordGapCenter + 381272 = fullRecordGapValue06832 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06832_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06832 (fullRecordGapValue06832 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06832_not_prime : ¬(recordGapCenter + 381272).Prime := by
  rw [fullRecordGapTerm06832_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06832, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06832_fast_pow_mod_ne_one

def fullRecordGapValue06833 : Nat := fullRecordGapCenterValue + 381308

theorem fullRecordGapTerm06833_eq_value :
    recordGapCenter + 381308 = fullRecordGapValue06833 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06833_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06833 (fullRecordGapValue06833 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06833_not_prime : ¬(recordGapCenter + 381308).Prime := by
  rw [fullRecordGapTerm06833_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06833, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06833_fast_pow_mod_ne_one

def fullRecordGapValue06834 : Nat := fullRecordGapCenterValue + 381356

theorem fullRecordGapTerm06834_eq_value :
    recordGapCenter + 381356 = fullRecordGapValue06834 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06834_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06834 (fullRecordGapValue06834 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06834_not_prime : ¬(recordGapCenter + 381356).Prime := by
  rw [fullRecordGapTerm06834_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06834, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06834_fast_pow_mod_ne_one

def fullRecordGapValue06835 : Nat := fullRecordGapCenterValue + 381522

theorem fullRecordGapTerm06835_eq_value :
    recordGapCenter + 381522 = fullRecordGapValue06835 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06835_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06835 (fullRecordGapValue06835 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06835_not_prime : ¬(recordGapCenter + 381522).Prime := by
  rw [fullRecordGapTerm06835_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06835, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06835_fast_pow_mod_ne_one

def fullRecordGapValue06836 : Nat := fullRecordGapCenterValue + 381566

theorem fullRecordGapTerm06836_eq_value :
    recordGapCenter + 381566 = fullRecordGapValue06836 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06836_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06836 (fullRecordGapValue06836 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06836_not_prime : ¬(recordGapCenter + 381566).Prime := by
  rw [fullRecordGapTerm06836_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06836, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06836_fast_pow_mod_ne_one

def fullRecordGapValue06837 : Nat := fullRecordGapCenterValue + 381572

theorem fullRecordGapTerm06837_eq_value :
    recordGapCenter + 381572 = fullRecordGapValue06837 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06837_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06837 (fullRecordGapValue06837 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06837_not_prime : ¬(recordGapCenter + 381572).Prime := by
  rw [fullRecordGapTerm06837_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06837, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06837_fast_pow_mod_ne_one

def fullRecordGapValue06838 : Nat := fullRecordGapCenterValue + 381606

theorem fullRecordGapTerm06838_eq_value :
    recordGapCenter + 381606 = fullRecordGapValue06838 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06838_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06838 (fullRecordGapValue06838 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06838_not_prime : ¬(recordGapCenter + 381606).Prime := by
  rw [fullRecordGapTerm06838_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06838, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06838_fast_pow_mod_ne_one

def fullRecordGapValue06839 : Nat := fullRecordGapCenterValue + 381782

theorem fullRecordGapTerm06839_eq_value :
    recordGapCenter + 381782 = fullRecordGapValue06839 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06839_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06839 (fullRecordGapValue06839 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06839_not_prime : ¬(recordGapCenter + 381782).Prime := by
  rw [fullRecordGapTerm06839_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06839, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06839_fast_pow_mod_ne_one

def fullRecordGapValue06840 : Nat := fullRecordGapCenterValue + 381882

theorem fullRecordGapTerm06840_eq_value :
    recordGapCenter + 381882 = fullRecordGapValue06840 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06840_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06840 (fullRecordGapValue06840 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06840_not_prime : ¬(recordGapCenter + 381882).Prime := by
  rw [fullRecordGapTerm06840_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06840, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06840_fast_pow_mod_ne_one

def fullRecordGapValue06841 : Nat := fullRecordGapCenterValue + 381896

theorem fullRecordGapTerm06841_eq_value :
    recordGapCenter + 381896 = fullRecordGapValue06841 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06841_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06841 (fullRecordGapValue06841 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06841_not_prime : ¬(recordGapCenter + 381896).Prime := by
  rw [fullRecordGapTerm06841_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06841, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06841_fast_pow_mod_ne_one

def fullRecordGapValue06842 : Nat := fullRecordGapCenterValue + 382002

theorem fullRecordGapTerm06842_eq_value :
    recordGapCenter + 382002 = fullRecordGapValue06842 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06842_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06842 (fullRecordGapValue06842 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06842_not_prime : ¬(recordGapCenter + 382002).Prime := by
  rw [fullRecordGapTerm06842_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06842, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06842_fast_pow_mod_ne_one

def fullRecordGapValue06843 : Nat := fullRecordGapCenterValue + 382142

theorem fullRecordGapTerm06843_eq_value :
    recordGapCenter + 382142 = fullRecordGapValue06843 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06843_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06843 (fullRecordGapValue06843 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06843_not_prime : ¬(recordGapCenter + 382142).Prime := by
  rw [fullRecordGapTerm06843_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06843, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06843_fast_pow_mod_ne_one

def fullRecordGapValue06844 : Nat := fullRecordGapCenterValue + 382218

theorem fullRecordGapTerm06844_eq_value :
    recordGapCenter + 382218 = fullRecordGapValue06844 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06844_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06844 (fullRecordGapValue06844 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06844_not_prime : ¬(recordGapCenter + 382218).Prime := by
  rw [fullRecordGapTerm06844_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06844, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06844_fast_pow_mod_ne_one

def fullRecordGapValue06845 : Nat := fullRecordGapCenterValue + 382232

theorem fullRecordGapTerm06845_eq_value :
    recordGapCenter + 382232 = fullRecordGapValue06845 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06845_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06845 (fullRecordGapValue06845 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06845_not_prime : ¬(recordGapCenter + 382232).Prime := by
  rw [fullRecordGapTerm06845_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06845, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06845_fast_pow_mod_ne_one

def fullRecordGapValue06846 : Nat := fullRecordGapCenterValue + 382238

theorem fullRecordGapTerm06846_eq_value :
    recordGapCenter + 382238 = fullRecordGapValue06846 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06846_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06846 (fullRecordGapValue06846 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06846_not_prime : ¬(recordGapCenter + 382238).Prime := by
  rw [fullRecordGapTerm06846_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06846, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06846_fast_pow_mod_ne_one

def fullRecordGapValue06847 : Nat := fullRecordGapCenterValue + 382286

theorem fullRecordGapTerm06847_eq_value :
    recordGapCenter + 382286 = fullRecordGapValue06847 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06847_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06847 (fullRecordGapValue06847 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06847_not_prime : ¬(recordGapCenter + 382286).Prime := by
  rw [fullRecordGapTerm06847_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06847, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06847_fast_pow_mod_ne_one

def fullRecordGapValue06848 : Nat := fullRecordGapCenterValue + 382362

theorem fullRecordGapTerm06848_eq_value :
    recordGapCenter + 382362 = fullRecordGapValue06848 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06848_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06848 (fullRecordGapValue06848 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06848_not_prime : ¬(recordGapCenter + 382362).Prime := by
  rw [fullRecordGapTerm06848_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06848, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06848_fast_pow_mod_ne_one

def fullRecordGapValue06849 : Nat := fullRecordGapCenterValue + 382566

theorem fullRecordGapTerm06849_eq_value :
    recordGapCenter + 382566 = fullRecordGapValue06849 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06849_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06849 (fullRecordGapValue06849 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06849_not_prime : ¬(recordGapCenter + 382566).Prime := by
  rw [fullRecordGapTerm06849_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06849, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06849_fast_pow_mod_ne_one

def fullRecordGapValue06850 : Nat := fullRecordGapCenterValue + 382638

theorem fullRecordGapTerm06850_eq_value :
    recordGapCenter + 382638 = fullRecordGapValue06850 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06850_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06850 (fullRecordGapValue06850 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06850_not_prime : ¬(recordGapCenter + 382638).Prime := by
  rw [fullRecordGapTerm06850_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06850, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06850_fast_pow_mod_ne_one

def fullRecordGapValue06851 : Nat := fullRecordGapCenterValue + 382856

theorem fullRecordGapTerm06851_eq_value :
    recordGapCenter + 382856 = fullRecordGapValue06851 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06851_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06851 (fullRecordGapValue06851 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06851_not_prime : ¬(recordGapCenter + 382856).Prime := by
  rw [fullRecordGapTerm06851_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06851, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06851_fast_pow_mod_ne_one

def fullRecordGapValue06852 : Nat := fullRecordGapCenterValue + 382868

theorem fullRecordGapTerm06852_eq_value :
    recordGapCenter + 382868 = fullRecordGapValue06852 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06852_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06852 (fullRecordGapValue06852 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06852_not_prime : ¬(recordGapCenter + 382868).Prime := by
  rw [fullRecordGapTerm06852_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06852, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06852_fast_pow_mod_ne_one

def fullRecordGapValue06853 : Nat := fullRecordGapCenterValue + 382898

theorem fullRecordGapTerm06853_eq_value :
    recordGapCenter + 382898 = fullRecordGapValue06853 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06853_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06853 (fullRecordGapValue06853 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06853_not_prime : ¬(recordGapCenter + 382898).Prime := by
  rw [fullRecordGapTerm06853_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06853, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06853_fast_pow_mod_ne_one

def fullRecordGapValue06854 : Nat := fullRecordGapCenterValue + 382946

theorem fullRecordGapTerm06854_eq_value :
    recordGapCenter + 382946 = fullRecordGapValue06854 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06854_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06854 (fullRecordGapValue06854 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06854_not_prime : ¬(recordGapCenter + 382946).Prime := by
  rw [fullRecordGapTerm06854_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06854, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06854_fast_pow_mod_ne_one

def fullRecordGapValue06855 : Nat := fullRecordGapCenterValue + 383048

theorem fullRecordGapTerm06855_eq_value :
    recordGapCenter + 383048 = fullRecordGapValue06855 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06855_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06855 (fullRecordGapValue06855 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06855_not_prime : ¬(recordGapCenter + 383048).Prime := by
  rw [fullRecordGapTerm06855_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06855, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06855_fast_pow_mod_ne_one

def fullRecordGapValue06856 : Nat := fullRecordGapCenterValue + 383066

theorem fullRecordGapTerm06856_eq_value :
    recordGapCenter + 383066 = fullRecordGapValue06856 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06856_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06856 (fullRecordGapValue06856 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06856_not_prime : ¬(recordGapCenter + 383066).Prime := by
  rw [fullRecordGapTerm06856_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06856, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06856_fast_pow_mod_ne_one

def fullRecordGapValue06857 : Nat := fullRecordGapCenterValue + 383132

theorem fullRecordGapTerm06857_eq_value :
    recordGapCenter + 383132 = fullRecordGapValue06857 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06857_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06857 (fullRecordGapValue06857 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06857_not_prime : ¬(recordGapCenter + 383132).Prime := by
  rw [fullRecordGapTerm06857_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06857, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06857_fast_pow_mod_ne_one

def fullRecordGapValue06858 : Nat := fullRecordGapCenterValue + 383178

theorem fullRecordGapTerm06858_eq_value :
    recordGapCenter + 383178 = fullRecordGapValue06858 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06858_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06858 (fullRecordGapValue06858 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06858_not_prime : ¬(recordGapCenter + 383178).Prime := by
  rw [fullRecordGapTerm06858_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06858, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06858_fast_pow_mod_ne_one

def fullRecordGapValue06859 : Nat := fullRecordGapCenterValue + 383198

theorem fullRecordGapTerm06859_eq_value :
    recordGapCenter + 383198 = fullRecordGapValue06859 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06859_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06859 (fullRecordGapValue06859 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06859_not_prime : ¬(recordGapCenter + 383198).Prime := by
  rw [fullRecordGapTerm06859_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06859, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06859_fast_pow_mod_ne_one

def fullRecordGapValue06860 : Nat := fullRecordGapCenterValue + 383252

theorem fullRecordGapTerm06860_eq_value :
    recordGapCenter + 383252 = fullRecordGapValue06860 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06860_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06860 (fullRecordGapValue06860 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06860_not_prime : ¬(recordGapCenter + 383252).Prime := by
  rw [fullRecordGapTerm06860_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06860, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06860_fast_pow_mod_ne_one

def fullRecordGapValue06861 : Nat := fullRecordGapCenterValue + 383288

theorem fullRecordGapTerm06861_eq_value :
    recordGapCenter + 383288 = fullRecordGapValue06861 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06861_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06861 (fullRecordGapValue06861 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06861_not_prime : ¬(recordGapCenter + 383288).Prime := by
  rw [fullRecordGapTerm06861_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06861, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06861_fast_pow_mod_ne_one

def fullRecordGapValue06862 : Nat := fullRecordGapCenterValue + 383328

theorem fullRecordGapTerm06862_eq_value :
    recordGapCenter + 383328 = fullRecordGapValue06862 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06862_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06862 (fullRecordGapValue06862 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06862_not_prime : ¬(recordGapCenter + 383328).Prime := by
  rw [fullRecordGapTerm06862_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06862, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06862_fast_pow_mod_ne_one

def fullRecordGapValue06863 : Nat := fullRecordGapCenterValue + 383336

theorem fullRecordGapTerm06863_eq_value :
    recordGapCenter + 383336 = fullRecordGapValue06863 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06863_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06863 (fullRecordGapValue06863 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06863_not_prime : ¬(recordGapCenter + 383336).Prime := by
  rw [fullRecordGapTerm06863_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06863, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06863_fast_pow_mod_ne_one

def fullRecordGapValue06864 : Nat := fullRecordGapCenterValue + 383406

theorem fullRecordGapTerm06864_eq_value :
    recordGapCenter + 383406 = fullRecordGapValue06864 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06864_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06864 (fullRecordGapValue06864 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06864_not_prime : ¬(recordGapCenter + 383406).Prime := by
  rw [fullRecordGapTerm06864_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06864, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06864_fast_pow_mod_ne_one

def fullRecordGapValue06865 : Nat := fullRecordGapCenterValue + 383442

theorem fullRecordGapTerm06865_eq_value :
    recordGapCenter + 383442 = fullRecordGapValue06865 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06865_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06865 (fullRecordGapValue06865 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06865_not_prime : ¬(recordGapCenter + 383442).Prime := by
  rw [fullRecordGapTerm06865_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06865, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06865_fast_pow_mod_ne_one

def fullRecordGapValue06866 : Nat := fullRecordGapCenterValue + 383498

theorem fullRecordGapTerm06866_eq_value :
    recordGapCenter + 383498 = fullRecordGapValue06866 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06866_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06866 (fullRecordGapValue06866 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06866_not_prime : ¬(recordGapCenter + 383498).Prime := by
  rw [fullRecordGapTerm06866_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06866, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06866_fast_pow_mod_ne_one

def fullRecordGapValue06867 : Nat := fullRecordGapCenterValue + 383546

theorem fullRecordGapTerm06867_eq_value :
    recordGapCenter + 383546 = fullRecordGapValue06867 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06867_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06867 (fullRecordGapValue06867 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06867_not_prime : ¬(recordGapCenter + 383546).Prime := by
  rw [fullRecordGapTerm06867_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06867, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06867_fast_pow_mod_ne_one

def fullRecordGapValue06868 : Nat := fullRecordGapCenterValue + 383828

theorem fullRecordGapTerm06868_eq_value :
    recordGapCenter + 383828 = fullRecordGapValue06868 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06868_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06868 (fullRecordGapValue06868 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06868_not_prime : ¬(recordGapCenter + 383828).Prime := by
  rw [fullRecordGapTerm06868_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06868, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06868_fast_pow_mod_ne_one

def fullRecordGapValue06869 : Nat := fullRecordGapCenterValue + 383906

theorem fullRecordGapTerm06869_eq_value :
    recordGapCenter + 383906 = fullRecordGapValue06869 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06869_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06869 (fullRecordGapValue06869 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06869_not_prime : ¬(recordGapCenter + 383906).Prime := by
  rw [fullRecordGapTerm06869_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06869, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06869_fast_pow_mod_ne_one

def fullRecordGapValue06870 : Nat := fullRecordGapCenterValue + 383982

theorem fullRecordGapTerm06870_eq_value :
    recordGapCenter + 383982 = fullRecordGapValue06870 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06870_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06870 (fullRecordGapValue06870 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06870_not_prime : ¬(recordGapCenter + 383982).Prime := by
  rw [fullRecordGapTerm06870_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06870, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06870_fast_pow_mod_ne_one

def fullRecordGapValue06871 : Nat := fullRecordGapCenterValue + 384000

theorem fullRecordGapTerm06871_eq_value :
    recordGapCenter + 384000 = fullRecordGapValue06871 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06871_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06871 (fullRecordGapValue06871 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06871_not_prime : ¬(recordGapCenter + 384000).Prime := by
  rw [fullRecordGapTerm06871_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06871, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06871_fast_pow_mod_ne_one

def fullRecordGapValue06872 : Nat := fullRecordGapCenterValue + 384086

theorem fullRecordGapTerm06872_eq_value :
    recordGapCenter + 384086 = fullRecordGapValue06872 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06872_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06872 (fullRecordGapValue06872 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06872_not_prime : ¬(recordGapCenter + 384086).Prime := by
  rw [fullRecordGapTerm06872_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06872, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06872_fast_pow_mod_ne_one

def fullRecordGapValue06873 : Nat := fullRecordGapCenterValue + 384198

theorem fullRecordGapTerm06873_eq_value :
    recordGapCenter + 384198 = fullRecordGapValue06873 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06873_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06873 (fullRecordGapValue06873 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06873_not_prime : ¬(recordGapCenter + 384198).Prime := by
  rw [fullRecordGapTerm06873_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06873, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06873_fast_pow_mod_ne_one

def fullRecordGapValue06874 : Nat := fullRecordGapCenterValue + 384242

theorem fullRecordGapTerm06874_eq_value :
    recordGapCenter + 384242 = fullRecordGapValue06874 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06874_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06874 (fullRecordGapValue06874 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06874_not_prime : ¬(recordGapCenter + 384242).Prime := by
  rw [fullRecordGapTerm06874_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06874, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06874_fast_pow_mod_ne_one

def fullRecordGapValue06875 : Nat := fullRecordGapCenterValue + 384378

theorem fullRecordGapTerm06875_eq_value :
    recordGapCenter + 384378 = fullRecordGapValue06875 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06875_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06875 (fullRecordGapValue06875 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06875_not_prime : ¬(recordGapCenter + 384378).Prime := by
  rw [fullRecordGapTerm06875_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06875, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06875_fast_pow_mod_ne_one

def fullRecordGapValue06876 : Nat := fullRecordGapCenterValue + 384458

theorem fullRecordGapTerm06876_eq_value :
    recordGapCenter + 384458 = fullRecordGapValue06876 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06876_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06876 (fullRecordGapValue06876 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06876_not_prime : ¬(recordGapCenter + 384458).Prime := by
  rw [fullRecordGapTerm06876_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06876, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06876_fast_pow_mod_ne_one

def fullRecordGapValue06877 : Nat := fullRecordGapCenterValue + 384518

theorem fullRecordGapTerm06877_eq_value :
    recordGapCenter + 384518 = fullRecordGapValue06877 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06877_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06877 (fullRecordGapValue06877 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06877_not_prime : ¬(recordGapCenter + 384518).Prime := by
  rw [fullRecordGapTerm06877_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06877, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06877_fast_pow_mod_ne_one

def fullRecordGapValue06878 : Nat := fullRecordGapCenterValue + 384542

theorem fullRecordGapTerm06878_eq_value :
    recordGapCenter + 384542 = fullRecordGapValue06878 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06878_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06878 (fullRecordGapValue06878 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06878_not_prime : ¬(recordGapCenter + 384542).Prime := by
  rw [fullRecordGapTerm06878_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06878, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06878_fast_pow_mod_ne_one

def fullRecordGapValue06879 : Nat := fullRecordGapCenterValue + 384546

theorem fullRecordGapTerm06879_eq_value :
    recordGapCenter + 384546 = fullRecordGapValue06879 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06879_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06879 (fullRecordGapValue06879 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06879_not_prime : ¬(recordGapCenter + 384546).Prime := by
  rw [fullRecordGapTerm06879_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06879, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06879_fast_pow_mod_ne_one

def fullRecordGapValue06880 : Nat := fullRecordGapCenterValue + 384548

theorem fullRecordGapTerm06880_eq_value :
    recordGapCenter + 384548 = fullRecordGapValue06880 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06880_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06880 (fullRecordGapValue06880 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06880_not_prime : ¬(recordGapCenter + 384548).Prime := by
  rw [fullRecordGapTerm06880_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06880, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06880_fast_pow_mod_ne_one

def fullRecordGapValue06881 : Nat := fullRecordGapCenterValue + 384596

theorem fullRecordGapTerm06881_eq_value :
    recordGapCenter + 384596 = fullRecordGapValue06881 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06881_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06881 (fullRecordGapValue06881 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06881_not_prime : ¬(recordGapCenter + 384596).Prime := by
  rw [fullRecordGapTerm06881_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06881, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06881_fast_pow_mod_ne_one

def fullRecordGapValue06882 : Nat := fullRecordGapCenterValue + 384632

theorem fullRecordGapTerm06882_eq_value :
    recordGapCenter + 384632 = fullRecordGapValue06882 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06882_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06882 (fullRecordGapValue06882 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06882_not_prime : ¬(recordGapCenter + 384632).Prime := by
  rw [fullRecordGapTerm06882_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06882, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06882_fast_pow_mod_ne_one

def fullRecordGapValue06883 : Nat := fullRecordGapCenterValue + 384638

theorem fullRecordGapTerm06883_eq_value :
    recordGapCenter + 384638 = fullRecordGapValue06883 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06883_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06883 (fullRecordGapValue06883 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06883_not_prime : ¬(recordGapCenter + 384638).Prime := by
  rw [fullRecordGapTerm06883_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06883, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06883_fast_pow_mod_ne_one

def fullRecordGapValue06884 : Nat := fullRecordGapCenterValue + 384912

theorem fullRecordGapTerm06884_eq_value :
    recordGapCenter + 384912 = fullRecordGapValue06884 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06884_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06884 (fullRecordGapValue06884 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06884_not_prime : ¬(recordGapCenter + 384912).Prime := by
  rw [fullRecordGapTerm06884_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06884, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06884_fast_pow_mod_ne_one

def fullRecordGapValue06885 : Nat := fullRecordGapCenterValue + 384918

theorem fullRecordGapTerm06885_eq_value :
    recordGapCenter + 384918 = fullRecordGapValue06885 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06885_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06885 (fullRecordGapValue06885 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06885_not_prime : ¬(recordGapCenter + 384918).Prime := by
  rw [fullRecordGapTerm06885_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06885, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06885_fast_pow_mod_ne_one

def fullRecordGapValue06886 : Nat := fullRecordGapCenterValue + 384968

theorem fullRecordGapTerm06886_eq_value :
    recordGapCenter + 384968 = fullRecordGapValue06886 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06886_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06886 (fullRecordGapValue06886 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06886_not_prime : ¬(recordGapCenter + 384968).Prime := by
  rw [fullRecordGapTerm06886_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06886, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06886_fast_pow_mod_ne_one

def fullRecordGapValue06887 : Nat := fullRecordGapCenterValue + 385166

theorem fullRecordGapTerm06887_eq_value :
    recordGapCenter + 385166 = fullRecordGapValue06887 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06887_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06887 (fullRecordGapValue06887 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06887_not_prime : ¬(recordGapCenter + 385166).Prime := by
  rw [fullRecordGapTerm06887_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06887, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06887_fast_pow_mod_ne_one

def fullRecordGapValue06888 : Nat := fullRecordGapCenterValue + 385302

theorem fullRecordGapTerm06888_eq_value :
    recordGapCenter + 385302 = fullRecordGapValue06888 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06888_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06888 (fullRecordGapValue06888 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06888_not_prime : ¬(recordGapCenter + 385302).Prime := by
  rw [fullRecordGapTerm06888_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06888, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06888_fast_pow_mod_ne_one

def fullRecordGapValue06889 : Nat := fullRecordGapCenterValue + 385316

theorem fullRecordGapTerm06889_eq_value :
    recordGapCenter + 385316 = fullRecordGapValue06889 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06889_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06889 (fullRecordGapValue06889 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06889_not_prime : ¬(recordGapCenter + 385316).Prime := by
  rw [fullRecordGapTerm06889_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06889, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06889_fast_pow_mod_ne_one

def fullRecordGapValue06890 : Nat := fullRecordGapCenterValue + 385386

theorem fullRecordGapTerm06890_eq_value :
    recordGapCenter + 385386 = fullRecordGapValue06890 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06890_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06890 (fullRecordGapValue06890 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06890_not_prime : ¬(recordGapCenter + 385386).Prime := by
  rw [fullRecordGapTerm06890_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06890, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06890_fast_pow_mod_ne_one

def fullRecordGapValue06891 : Nat := fullRecordGapCenterValue + 385508

theorem fullRecordGapTerm06891_eq_value :
    recordGapCenter + 385508 = fullRecordGapValue06891 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06891_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06891 (fullRecordGapValue06891 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06891_not_prime : ¬(recordGapCenter + 385508).Prime := by
  rw [fullRecordGapTerm06891_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06891, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06891_fast_pow_mod_ne_one

def fullRecordGapValue06892 : Nat := fullRecordGapCenterValue + 385676

theorem fullRecordGapTerm06892_eq_value :
    recordGapCenter + 385676 = fullRecordGapValue06892 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06892_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06892 (fullRecordGapValue06892 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06892_not_prime : ¬(recordGapCenter + 385676).Prime := by
  rw [fullRecordGapTerm06892_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06892, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06892_fast_pow_mod_ne_one

def fullRecordGapValue06893 : Nat := fullRecordGapCenterValue + 385772

theorem fullRecordGapTerm06893_eq_value :
    recordGapCenter + 385772 = fullRecordGapValue06893 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06893_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06893 (fullRecordGapValue06893 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06893_not_prime : ¬(recordGapCenter + 385772).Prime := by
  rw [fullRecordGapTerm06893_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06893, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06893_fast_pow_mod_ne_one

def fullRecordGapValue06894 : Nat := fullRecordGapCenterValue + 386018

theorem fullRecordGapTerm06894_eq_value :
    recordGapCenter + 386018 = fullRecordGapValue06894 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06894_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06894 (fullRecordGapValue06894 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06894_not_prime : ¬(recordGapCenter + 386018).Prime := by
  rw [fullRecordGapTerm06894_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06894, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06894_fast_pow_mod_ne_one

def fullRecordGapValue06895 : Nat := fullRecordGapCenterValue + 386108

theorem fullRecordGapTerm06895_eq_value :
    recordGapCenter + 386108 = fullRecordGapValue06895 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06895_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06895 (fullRecordGapValue06895 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06895_not_prime : ¬(recordGapCenter + 386108).Prime := by
  rw [fullRecordGapTerm06895_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06895, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06895_fast_pow_mod_ne_one

def fullRecordGapValue06896 : Nat := fullRecordGapCenterValue + 386186

theorem fullRecordGapTerm06896_eq_value :
    recordGapCenter + 386186 = fullRecordGapValue06896 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06896_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06896 (fullRecordGapValue06896 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06896_not_prime : ¬(recordGapCenter + 386186).Prime := by
  rw [fullRecordGapTerm06896_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06896, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06896_fast_pow_mod_ne_one

def fullRecordGapValue06897 : Nat := fullRecordGapCenterValue + 386286

theorem fullRecordGapTerm06897_eq_value :
    recordGapCenter + 386286 = fullRecordGapValue06897 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06897_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06897 (fullRecordGapValue06897 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06897_not_prime : ¬(recordGapCenter + 386286).Prime := by
  rw [fullRecordGapTerm06897_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06897, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06897_fast_pow_mod_ne_one

def fullRecordGapValue06898 : Nat := fullRecordGapCenterValue + 386306

theorem fullRecordGapTerm06898_eq_value :
    recordGapCenter + 386306 = fullRecordGapValue06898 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06898_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06898 (fullRecordGapValue06898 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06898_not_prime : ¬(recordGapCenter + 386306).Prime := by
  rw [fullRecordGapTerm06898_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06898, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06898_fast_pow_mod_ne_one

def fullRecordGapValue06899 : Nat := fullRecordGapCenterValue + 386402

theorem fullRecordGapTerm06899_eq_value :
    recordGapCenter + 386402 = fullRecordGapValue06899 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06899_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06899 (fullRecordGapValue06899 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06899_not_prime : ¬(recordGapCenter + 386402).Prime := by
  rw [fullRecordGapTerm06899_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06899, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06899_fast_pow_mod_ne_one

def fullRecordGapValue06900 : Nat := fullRecordGapCenterValue + 386418

theorem fullRecordGapTerm06900_eq_value :
    recordGapCenter + 386418 = fullRecordGapValue06900 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06900_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06900 (fullRecordGapValue06900 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06900_not_prime : ¬(recordGapCenter + 386418).Prime := by
  rw [fullRecordGapTerm06900_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06900, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06900_fast_pow_mod_ne_one

def fullRecordGapValue06901 : Nat := fullRecordGapCenterValue + 386696

theorem fullRecordGapTerm06901_eq_value :
    recordGapCenter + 386696 = fullRecordGapValue06901 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06901_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06901 (fullRecordGapValue06901 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06901_not_prime : ¬(recordGapCenter + 386696).Prime := by
  rw [fullRecordGapTerm06901_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06901, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06901_fast_pow_mod_ne_one

def fullRecordGapValue06902 : Nat := fullRecordGapCenterValue + 386706

theorem fullRecordGapTerm06902_eq_value :
    recordGapCenter + 386706 = fullRecordGapValue06902 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06902_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06902 (fullRecordGapValue06902 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06902_not_prime : ¬(recordGapCenter + 386706).Prime := by
  rw [fullRecordGapTerm06902_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06902, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06902_fast_pow_mod_ne_one

def fullRecordGapValue06903 : Nat := fullRecordGapCenterValue + 386898

theorem fullRecordGapTerm06903_eq_value :
    recordGapCenter + 386898 = fullRecordGapValue06903 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06903_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06903 (fullRecordGapValue06903 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06903_not_prime : ¬(recordGapCenter + 386898).Prime := by
  rw [fullRecordGapTerm06903_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06903, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06903_fast_pow_mod_ne_one

def fullRecordGapValue06904 : Nat := fullRecordGapCenterValue + 387026

theorem fullRecordGapTerm06904_eq_value :
    recordGapCenter + 387026 = fullRecordGapValue06904 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06904_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06904 (fullRecordGapValue06904 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06904_not_prime : ¬(recordGapCenter + 387026).Prime := by
  rw [fullRecordGapTerm06904_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06904, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06904_fast_pow_mod_ne_one

def fullRecordGapValue06905 : Nat := fullRecordGapCenterValue + 387116

theorem fullRecordGapTerm06905_eq_value :
    recordGapCenter + 387116 = fullRecordGapValue06905 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06905_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06905 (fullRecordGapValue06905 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06905_not_prime : ¬(recordGapCenter + 387116).Prime := by
  rw [fullRecordGapTerm06905_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06905, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06905_fast_pow_mod_ne_one

def fullRecordGapValue06906 : Nat := fullRecordGapCenterValue + 387188

theorem fullRecordGapTerm06906_eq_value :
    recordGapCenter + 387188 = fullRecordGapValue06906 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06906_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06906 (fullRecordGapValue06906 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06906_not_prime : ¬(recordGapCenter + 387188).Prime := by
  rw [fullRecordGapTerm06906_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06906, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06906_fast_pow_mod_ne_one

def fullRecordGapValue06907 : Nat := fullRecordGapCenterValue + 387200

theorem fullRecordGapTerm06907_eq_value :
    recordGapCenter + 387200 = fullRecordGapValue06907 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06907_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06907 (fullRecordGapValue06907 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06907_not_prime : ¬(recordGapCenter + 387200).Prime := by
  rw [fullRecordGapTerm06907_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06907, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06907_fast_pow_mod_ne_one

def fullRecordGapValue06908 : Nat := fullRecordGapCenterValue + 387272

theorem fullRecordGapTerm06908_eq_value :
    recordGapCenter + 387272 = fullRecordGapValue06908 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06908_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06908 (fullRecordGapValue06908 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06908_not_prime : ¬(recordGapCenter + 387272).Prime := by
  rw [fullRecordGapTerm06908_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06908, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06908_fast_pow_mod_ne_one

def fullRecordGapValue06909 : Nat := fullRecordGapCenterValue + 387308

theorem fullRecordGapTerm06909_eq_value :
    recordGapCenter + 387308 = fullRecordGapValue06909 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06909_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06909 (fullRecordGapValue06909 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06909_not_prime : ¬(recordGapCenter + 387308).Prime := by
  rw [fullRecordGapTerm06909_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06909, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06909_fast_pow_mod_ne_one

def fullRecordGapValue06910 : Nat := fullRecordGapCenterValue + 387318

theorem fullRecordGapTerm06910_eq_value :
    recordGapCenter + 387318 = fullRecordGapValue06910 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06910_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06910 (fullRecordGapValue06910 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06910_not_prime : ¬(recordGapCenter + 387318).Prime := by
  rw [fullRecordGapTerm06910_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06910, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06910_fast_pow_mod_ne_one

def fullRecordGapValue06911 : Nat := fullRecordGapCenterValue + 387402

theorem fullRecordGapTerm06911_eq_value :
    recordGapCenter + 387402 = fullRecordGapValue06911 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06911_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06911 (fullRecordGapValue06911 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06911_not_prime : ¬(recordGapCenter + 387402).Prime := by
  rw [fullRecordGapTerm06911_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06911, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06911_fast_pow_mod_ne_one

def fullRecordGapValue06912 : Nat := fullRecordGapCenterValue + 387446

theorem fullRecordGapTerm06912_eq_value :
    recordGapCenter + 387446 = fullRecordGapValue06912 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral06912_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue06912 (fullRecordGapValue06912 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm06912_not_prime : ¬(recordGapCenter + 387446).Prime := by
  rw [fullRecordGapTerm06912_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue06912, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral06912_fast_pow_mod_ne_one

end PrimeFactorUnimodality
