import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue08705 : Nat := fullRecordGapCenterValue + 520826

theorem fullRecordGapTerm08705_eq_value :
    recordGapCenter + 520826 = fullRecordGapValue08705 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08705_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08705 (fullRecordGapValue08705 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08705_not_prime : ¬(recordGapCenter + 520826).Prime := by
  rw [fullRecordGapTerm08705_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08705, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08705_fast_pow_mod_ne_one

def fullRecordGapValue08706 : Nat := fullRecordGapCenterValue + 520838

theorem fullRecordGapTerm08706_eq_value :
    recordGapCenter + 520838 = fullRecordGapValue08706 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08706_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08706 (fullRecordGapValue08706 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08706_not_prime : ¬(recordGapCenter + 520838).Prime := by
  rw [fullRecordGapTerm08706_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08706, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08706_fast_pow_mod_ne_one

def fullRecordGapValue08707 : Nat := fullRecordGapCenterValue + 520892

theorem fullRecordGapTerm08707_eq_value :
    recordGapCenter + 520892 = fullRecordGapValue08707 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08707_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08707 (fullRecordGapValue08707 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08707_not_prime : ¬(recordGapCenter + 520892).Prime := by
  rw [fullRecordGapTerm08707_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08707, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08707_fast_pow_mod_ne_one

def fullRecordGapValue08708 : Nat := fullRecordGapCenterValue + 520922

theorem fullRecordGapTerm08708_eq_value :
    recordGapCenter + 520922 = fullRecordGapValue08708 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08708_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08708 (fullRecordGapValue08708 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08708_not_prime : ¬(recordGapCenter + 520922).Prime := by
  rw [fullRecordGapTerm08708_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08708, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08708_fast_pow_mod_ne_one

def fullRecordGapValue08709 : Nat := fullRecordGapCenterValue + 520952

theorem fullRecordGapTerm08709_eq_value :
    recordGapCenter + 520952 = fullRecordGapValue08709 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08709_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08709 (fullRecordGapValue08709 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08709_not_prime : ¬(recordGapCenter + 520952).Prime := by
  rw [fullRecordGapTerm08709_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08709, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08709_fast_pow_mod_ne_one

def fullRecordGapValue08710 : Nat := fullRecordGapCenterValue + 521012

theorem fullRecordGapTerm08710_eq_value :
    recordGapCenter + 521012 = fullRecordGapValue08710 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08710_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08710 (fullRecordGapValue08710 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08710_not_prime : ¬(recordGapCenter + 521012).Prime := by
  rw [fullRecordGapTerm08710_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08710, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08710_fast_pow_mod_ne_one

def fullRecordGapValue08711 : Nat := fullRecordGapCenterValue + 521102

theorem fullRecordGapTerm08711_eq_value :
    recordGapCenter + 521102 = fullRecordGapValue08711 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08711_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08711 (fullRecordGapValue08711 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08711_not_prime : ¬(recordGapCenter + 521102).Prime := by
  rw [fullRecordGapTerm08711_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08711, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08711_fast_pow_mod_ne_one

def fullRecordGapValue08712 : Nat := fullRecordGapCenterValue + 521106

theorem fullRecordGapTerm08712_eq_value :
    recordGapCenter + 521106 = fullRecordGapValue08712 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08712_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08712 (fullRecordGapValue08712 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08712_not_prime : ¬(recordGapCenter + 521106).Prime := by
  rw [fullRecordGapTerm08712_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08712, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08712_fast_pow_mod_ne_one

def fullRecordGapValue08713 : Nat := fullRecordGapCenterValue + 521166

theorem fullRecordGapTerm08713_eq_value :
    recordGapCenter + 521166 = fullRecordGapValue08713 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08713_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08713 (fullRecordGapValue08713 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08713_not_prime : ¬(recordGapCenter + 521166).Prime := by
  rw [fullRecordGapTerm08713_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08713, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08713_fast_pow_mod_ne_one

def fullRecordGapValue08714 : Nat := fullRecordGapCenterValue + 521210

theorem fullRecordGapTerm08714_eq_value :
    recordGapCenter + 521210 = fullRecordGapValue08714 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08714_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08714 (fullRecordGapValue08714 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08714_not_prime : ¬(recordGapCenter + 521210).Prime := by
  rw [fullRecordGapTerm08714_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08714, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08714_fast_pow_mod_ne_one

def fullRecordGapValue08715 : Nat := fullRecordGapCenterValue + 521258

theorem fullRecordGapTerm08715_eq_value :
    recordGapCenter + 521258 = fullRecordGapValue08715 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08715_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08715 (fullRecordGapValue08715 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08715_not_prime : ¬(recordGapCenter + 521258).Prime := by
  rw [fullRecordGapTerm08715_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08715, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08715_fast_pow_mod_ne_one

def fullRecordGapValue08716 : Nat := fullRecordGapCenterValue + 521270

theorem fullRecordGapTerm08716_eq_value :
    recordGapCenter + 521270 = fullRecordGapValue08716 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08716_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08716 (fullRecordGapValue08716 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08716_not_prime : ¬(recordGapCenter + 521270).Prime := by
  rw [fullRecordGapTerm08716_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08716, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08716_fast_pow_mod_ne_one

def fullRecordGapValue08717 : Nat := fullRecordGapCenterValue + 521336

theorem fullRecordGapTerm08717_eq_value :
    recordGapCenter + 521336 = fullRecordGapValue08717 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08717_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08717 (fullRecordGapValue08717 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08717_not_prime : ¬(recordGapCenter + 521336).Prime := by
  rw [fullRecordGapTerm08717_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08717, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08717_fast_pow_mod_ne_one

def fullRecordGapValue08718 : Nat := fullRecordGapCenterValue + 521426

theorem fullRecordGapTerm08718_eq_value :
    recordGapCenter + 521426 = fullRecordGapValue08718 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08718_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08718 (fullRecordGapValue08718 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08718_not_prime : ¬(recordGapCenter + 521426).Prime := by
  rw [fullRecordGapTerm08718_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08718, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08718_fast_pow_mod_ne_one

def fullRecordGapValue08719 : Nat := fullRecordGapCenterValue + 521516

theorem fullRecordGapTerm08719_eq_value :
    recordGapCenter + 521516 = fullRecordGapValue08719 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08719_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08719 (fullRecordGapValue08719 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08719_not_prime : ¬(recordGapCenter + 521516).Prime := by
  rw [fullRecordGapTerm08719_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08719, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08719_fast_pow_mod_ne_one

def fullRecordGapValue08720 : Nat := fullRecordGapCenterValue + 521522

theorem fullRecordGapTerm08720_eq_value :
    recordGapCenter + 521522 = fullRecordGapValue08720 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08720_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08720 (fullRecordGapValue08720 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08720_not_prime : ¬(recordGapCenter + 521522).Prime := by
  rw [fullRecordGapTerm08720_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08720, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08720_fast_pow_mod_ne_one

def fullRecordGapValue08721 : Nat := fullRecordGapCenterValue + 521538

theorem fullRecordGapTerm08721_eq_value :
    recordGapCenter + 521538 = fullRecordGapValue08721 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08721_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08721 (fullRecordGapValue08721 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08721_not_prime : ¬(recordGapCenter + 521538).Prime := by
  rw [fullRecordGapTerm08721_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08721, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08721_fast_pow_mod_ne_one

def fullRecordGapValue08722 : Nat := fullRecordGapCenterValue + 521582

theorem fullRecordGapTerm08722_eq_value :
    recordGapCenter + 521582 = fullRecordGapValue08722 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08722_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08722 (fullRecordGapValue08722 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08722_not_prime : ¬(recordGapCenter + 521582).Prime := by
  rw [fullRecordGapTerm08722_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08722, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08722_fast_pow_mod_ne_one

def fullRecordGapValue08723 : Nat := fullRecordGapCenterValue + 521630

theorem fullRecordGapTerm08723_eq_value :
    recordGapCenter + 521630 = fullRecordGapValue08723 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08723_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08723 (fullRecordGapValue08723 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08723_not_prime : ¬(recordGapCenter + 521630).Prime := by
  rw [fullRecordGapTerm08723_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08723, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08723_fast_pow_mod_ne_one

def fullRecordGapValue08724 : Nat := fullRecordGapCenterValue + 521810

theorem fullRecordGapTerm08724_eq_value :
    recordGapCenter + 521810 = fullRecordGapValue08724 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08724_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08724 (fullRecordGapValue08724 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08724_not_prime : ¬(recordGapCenter + 521810).Prime := by
  rw [fullRecordGapTerm08724_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08724, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08724_fast_pow_mod_ne_one

def fullRecordGapValue08725 : Nat := fullRecordGapCenterValue + 521876

theorem fullRecordGapTerm08725_eq_value :
    recordGapCenter + 521876 = fullRecordGapValue08725 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08725_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08725 (fullRecordGapValue08725 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08725_not_prime : ¬(recordGapCenter + 521876).Prime := by
  rw [fullRecordGapTerm08725_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08725, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08725_fast_pow_mod_ne_one

def fullRecordGapValue08726 : Nat := fullRecordGapCenterValue + 521882

theorem fullRecordGapTerm08726_eq_value :
    recordGapCenter + 521882 = fullRecordGapValue08726 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08726_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08726 (fullRecordGapValue08726 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08726_not_prime : ¬(recordGapCenter + 521882).Prime := by
  rw [fullRecordGapTerm08726_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08726, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08726_fast_pow_mod_ne_one

def fullRecordGapValue08727 : Nat := fullRecordGapCenterValue + 521958

theorem fullRecordGapTerm08727_eq_value :
    recordGapCenter + 521958 = fullRecordGapValue08727 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08727_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08727 (fullRecordGapValue08727 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08727_not_prime : ¬(recordGapCenter + 521958).Prime := by
  rw [fullRecordGapTerm08727_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08727, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08727_fast_pow_mod_ne_one

def fullRecordGapValue08728 : Nat := fullRecordGapCenterValue + 521988

theorem fullRecordGapTerm08728_eq_value :
    recordGapCenter + 521988 = fullRecordGapValue08728 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08728_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08728 (fullRecordGapValue08728 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08728_not_prime : ¬(recordGapCenter + 521988).Prime := by
  rw [fullRecordGapTerm08728_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08728, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08728_fast_pow_mod_ne_one

def fullRecordGapValue08729 : Nat := fullRecordGapCenterValue + 522026

theorem fullRecordGapTerm08729_eq_value :
    recordGapCenter + 522026 = fullRecordGapValue08729 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08729_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08729 (fullRecordGapValue08729 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08729_not_prime : ¬(recordGapCenter + 522026).Prime := by
  rw [fullRecordGapTerm08729_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08729, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08729_fast_pow_mod_ne_one

def fullRecordGapValue08730 : Nat := fullRecordGapCenterValue + 522068

theorem fullRecordGapTerm08730_eq_value :
    recordGapCenter + 522068 = fullRecordGapValue08730 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08730_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08730 (fullRecordGapValue08730 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08730_not_prime : ¬(recordGapCenter + 522068).Prime := by
  rw [fullRecordGapTerm08730_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08730, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08730_fast_pow_mod_ne_one

def fullRecordGapValue08731 : Nat := fullRecordGapCenterValue + 522092

theorem fullRecordGapTerm08731_eq_value :
    recordGapCenter + 522092 = fullRecordGapValue08731 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08731_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08731 (fullRecordGapValue08731 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08731_not_prime : ¬(recordGapCenter + 522092).Prime := by
  rw [fullRecordGapTerm08731_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08731, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08731_fast_pow_mod_ne_one

def fullRecordGapValue08732 : Nat := fullRecordGapCenterValue + 522152

theorem fullRecordGapTerm08732_eq_value :
    recordGapCenter + 522152 = fullRecordGapValue08732 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08732_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08732 (fullRecordGapValue08732 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08732_not_prime : ¬(recordGapCenter + 522152).Prime := by
  rw [fullRecordGapTerm08732_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08732, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08732_fast_pow_mod_ne_one

def fullRecordGapValue08733 : Nat := fullRecordGapCenterValue + 522212

theorem fullRecordGapTerm08733_eq_value :
    recordGapCenter + 522212 = fullRecordGapValue08733 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08733_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08733 (fullRecordGapValue08733 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08733_not_prime : ¬(recordGapCenter + 522212).Prime := by
  rw [fullRecordGapTerm08733_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08733, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08733_fast_pow_mod_ne_one

def fullRecordGapValue08734 : Nat := fullRecordGapCenterValue + 522230

theorem fullRecordGapTerm08734_eq_value :
    recordGapCenter + 522230 = fullRecordGapValue08734 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08734_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08734 (fullRecordGapValue08734 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08734_not_prime : ¬(recordGapCenter + 522230).Prime := by
  rw [fullRecordGapTerm08734_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08734, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08734_fast_pow_mod_ne_one

def fullRecordGapValue08735 : Nat := fullRecordGapCenterValue + 522296

theorem fullRecordGapTerm08735_eq_value :
    recordGapCenter + 522296 = fullRecordGapValue08735 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08735_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08735 (fullRecordGapValue08735 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08735_not_prime : ¬(recordGapCenter + 522296).Prime := by
  rw [fullRecordGapTerm08735_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08735, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08735_fast_pow_mod_ne_one

def fullRecordGapValue08736 : Nat := fullRecordGapCenterValue + 522476

theorem fullRecordGapTerm08736_eq_value :
    recordGapCenter + 522476 = fullRecordGapValue08736 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08736_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08736 (fullRecordGapValue08736 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08736_not_prime : ¬(recordGapCenter + 522476).Prime := by
  rw [fullRecordGapTerm08736_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08736, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08736_fast_pow_mod_ne_one

def fullRecordGapValue08737 : Nat := fullRecordGapCenterValue + 522498

theorem fullRecordGapTerm08737_eq_value :
    recordGapCenter + 522498 = fullRecordGapValue08737 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08737_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08737 (fullRecordGapValue08737 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08737_not_prime : ¬(recordGapCenter + 522498).Prime := by
  rw [fullRecordGapTerm08737_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08737, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08737_fast_pow_mod_ne_one

def fullRecordGapValue08738 : Nat := fullRecordGapCenterValue + 522572

theorem fullRecordGapTerm08738_eq_value :
    recordGapCenter + 522572 = fullRecordGapValue08738 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08738_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08738 (fullRecordGapValue08738 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08738_not_prime : ¬(recordGapCenter + 522572).Prime := by
  rw [fullRecordGapTerm08738_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08738, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08738_fast_pow_mod_ne_one

def fullRecordGapValue08739 : Nat := fullRecordGapCenterValue + 522590

theorem fullRecordGapTerm08739_eq_value :
    recordGapCenter + 522590 = fullRecordGapValue08739 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08739_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08739 (fullRecordGapValue08739 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08739_not_prime : ¬(recordGapCenter + 522590).Prime := by
  rw [fullRecordGapTerm08739_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08739, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08739_fast_pow_mod_ne_one

def fullRecordGapValue08740 : Nat := fullRecordGapCenterValue + 522596

theorem fullRecordGapTerm08740_eq_value :
    recordGapCenter + 522596 = fullRecordGapValue08740 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08740_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08740 (fullRecordGapValue08740 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08740_not_prime : ¬(recordGapCenter + 522596).Prime := by
  rw [fullRecordGapTerm08740_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08740, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08740_fast_pow_mod_ne_one

def fullRecordGapValue08741 : Nat := fullRecordGapCenterValue + 522720

theorem fullRecordGapTerm08741_eq_value :
    recordGapCenter + 522720 = fullRecordGapValue08741 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08741_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08741 (fullRecordGapValue08741 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08741_not_prime : ¬(recordGapCenter + 522720).Prime := by
  rw [fullRecordGapTerm08741_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08741, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08741_fast_pow_mod_ne_one

def fullRecordGapValue08742 : Nat := fullRecordGapCenterValue + 522758

theorem fullRecordGapTerm08742_eq_value :
    recordGapCenter + 522758 = fullRecordGapValue08742 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08742_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08742 (fullRecordGapValue08742 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08742_not_prime : ¬(recordGapCenter + 522758).Prime := by
  rw [fullRecordGapTerm08742_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08742, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08742_fast_pow_mod_ne_one

def fullRecordGapValue08743 : Nat := fullRecordGapCenterValue + 522876

theorem fullRecordGapTerm08743_eq_value :
    recordGapCenter + 522876 = fullRecordGapValue08743 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08743_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08743 (fullRecordGapValue08743 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08743_not_prime : ¬(recordGapCenter + 522876).Prime := by
  rw [fullRecordGapTerm08743_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08743, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08743_fast_pow_mod_ne_one

def fullRecordGapValue08744 : Nat := fullRecordGapCenterValue + 522902

theorem fullRecordGapTerm08744_eq_value :
    recordGapCenter + 522902 = fullRecordGapValue08744 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08744_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08744 (fullRecordGapValue08744 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08744_not_prime : ¬(recordGapCenter + 522902).Prime := by
  rw [fullRecordGapTerm08744_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08744, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08744_fast_pow_mod_ne_one

def fullRecordGapValue08745 : Nat := fullRecordGapCenterValue + 522926

theorem fullRecordGapTerm08745_eq_value :
    recordGapCenter + 522926 = fullRecordGapValue08745 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08745_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08745 (fullRecordGapValue08745 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08745_not_prime : ¬(recordGapCenter + 522926).Prime := by
  rw [fullRecordGapTerm08745_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08745, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08745_fast_pow_mod_ne_one

def fullRecordGapValue08746 : Nat := fullRecordGapCenterValue + 523058

theorem fullRecordGapTerm08746_eq_value :
    recordGapCenter + 523058 = fullRecordGapValue08746 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08746_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08746 (fullRecordGapValue08746 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08746_not_prime : ¬(recordGapCenter + 523058).Prime := by
  rw [fullRecordGapTerm08746_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08746, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08746_fast_pow_mod_ne_one

def fullRecordGapValue08747 : Nat := fullRecordGapCenterValue + 523076

theorem fullRecordGapTerm08747_eq_value :
    recordGapCenter + 523076 = fullRecordGapValue08747 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08747_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08747 (fullRecordGapValue08747 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08747_not_prime : ¬(recordGapCenter + 523076).Prime := by
  rw [fullRecordGapTerm08747_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08747, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08747_fast_pow_mod_ne_one

def fullRecordGapValue08748 : Nat := fullRecordGapCenterValue + 523148

theorem fullRecordGapTerm08748_eq_value :
    recordGapCenter + 523148 = fullRecordGapValue08748 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08748_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08748 (fullRecordGapValue08748 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08748_not_prime : ¬(recordGapCenter + 523148).Prime := by
  rw [fullRecordGapTerm08748_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08748, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08748_fast_pow_mod_ne_one

def fullRecordGapValue08749 : Nat := fullRecordGapCenterValue + 523262

theorem fullRecordGapTerm08749_eq_value :
    recordGapCenter + 523262 = fullRecordGapValue08749 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08749_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08749 (fullRecordGapValue08749 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08749_not_prime : ¬(recordGapCenter + 523262).Prime := by
  rw [fullRecordGapTerm08749_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08749, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08749_fast_pow_mod_ne_one

def fullRecordGapValue08750 : Nat := fullRecordGapCenterValue + 523268

theorem fullRecordGapTerm08750_eq_value :
    recordGapCenter + 523268 = fullRecordGapValue08750 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08750_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08750 (fullRecordGapValue08750 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08750_not_prime : ¬(recordGapCenter + 523268).Prime := by
  rw [fullRecordGapTerm08750_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08750, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08750_fast_pow_mod_ne_one

def fullRecordGapValue08751 : Nat := fullRecordGapCenterValue + 523316

theorem fullRecordGapTerm08751_eq_value :
    recordGapCenter + 523316 = fullRecordGapValue08751 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08751_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08751 (fullRecordGapValue08751 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08751_not_prime : ¬(recordGapCenter + 523316).Prime := by
  rw [fullRecordGapTerm08751_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08751, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08751_fast_pow_mod_ne_one

def fullRecordGapValue08752 : Nat := fullRecordGapCenterValue + 523436

theorem fullRecordGapTerm08752_eq_value :
    recordGapCenter + 523436 = fullRecordGapValue08752 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08752_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08752 (fullRecordGapValue08752 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08752_not_prime : ¬(recordGapCenter + 523436).Prime := by
  rw [fullRecordGapTerm08752_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08752, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08752_fast_pow_mod_ne_one

def fullRecordGapValue08753 : Nat := fullRecordGapCenterValue + 523646

theorem fullRecordGapTerm08753_eq_value :
    recordGapCenter + 523646 = fullRecordGapValue08753 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08753_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08753 (fullRecordGapValue08753 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08753_not_prime : ¬(recordGapCenter + 523646).Prime := by
  rw [fullRecordGapTerm08753_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08753, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08753_fast_pow_mod_ne_one

def fullRecordGapValue08754 : Nat := fullRecordGapCenterValue + 523758

theorem fullRecordGapTerm08754_eq_value :
    recordGapCenter + 523758 = fullRecordGapValue08754 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08754_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08754 (fullRecordGapValue08754 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08754_not_prime : ¬(recordGapCenter + 523758).Prime := by
  rw [fullRecordGapTerm08754_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08754, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08754_fast_pow_mod_ne_one

def fullRecordGapValue08755 : Nat := fullRecordGapCenterValue + 523790

theorem fullRecordGapTerm08755_eq_value :
    recordGapCenter + 523790 = fullRecordGapValue08755 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08755_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08755 (fullRecordGapValue08755 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08755_not_prime : ¬(recordGapCenter + 523790).Prime := by
  rw [fullRecordGapTerm08755_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08755, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08755_fast_pow_mod_ne_one

def fullRecordGapValue08756 : Nat := fullRecordGapCenterValue + 523812

theorem fullRecordGapTerm08756_eq_value :
    recordGapCenter + 523812 = fullRecordGapValue08756 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08756_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08756 (fullRecordGapValue08756 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08756_not_prime : ¬(recordGapCenter + 523812).Prime := by
  rw [fullRecordGapTerm08756_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08756, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08756_fast_pow_mod_ne_one

def fullRecordGapValue08757 : Nat := fullRecordGapCenterValue + 523832

theorem fullRecordGapTerm08757_eq_value :
    recordGapCenter + 523832 = fullRecordGapValue08757 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08757_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08757 (fullRecordGapValue08757 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08757_not_prime : ¬(recordGapCenter + 523832).Prime := by
  rw [fullRecordGapTerm08757_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08757, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08757_fast_pow_mod_ne_one

def fullRecordGapValue08758 : Nat := fullRecordGapCenterValue + 523938

theorem fullRecordGapTerm08758_eq_value :
    recordGapCenter + 523938 = fullRecordGapValue08758 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08758_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08758 (fullRecordGapValue08758 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08758_not_prime : ¬(recordGapCenter + 523938).Prime := by
  rw [fullRecordGapTerm08758_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08758, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08758_fast_pow_mod_ne_one

def fullRecordGapValue08759 : Nat := fullRecordGapCenterValue + 523946

theorem fullRecordGapTerm08759_eq_value :
    recordGapCenter + 523946 = fullRecordGapValue08759 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08759_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08759 (fullRecordGapValue08759 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08759_not_prime : ¬(recordGapCenter + 523946).Prime := by
  rw [fullRecordGapTerm08759_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08759, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08759_fast_pow_mod_ne_one

def fullRecordGapValue08760 : Nat := fullRecordGapCenterValue + 524252

theorem fullRecordGapTerm08760_eq_value :
    recordGapCenter + 524252 = fullRecordGapValue08760 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08760_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08760 (fullRecordGapValue08760 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08760_not_prime : ¬(recordGapCenter + 524252).Prime := by
  rw [fullRecordGapTerm08760_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08760, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08760_fast_pow_mod_ne_one

def fullRecordGapValue08761 : Nat := fullRecordGapCenterValue + 524408

theorem fullRecordGapTerm08761_eq_value :
    recordGapCenter + 524408 = fullRecordGapValue08761 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08761_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08761 (fullRecordGapValue08761 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08761_not_prime : ¬(recordGapCenter + 524408).Prime := by
  rw [fullRecordGapTerm08761_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08761, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08761_fast_pow_mod_ne_one

def fullRecordGapValue08762 : Nat := fullRecordGapCenterValue + 524562

theorem fullRecordGapTerm08762_eq_value :
    recordGapCenter + 524562 = fullRecordGapValue08762 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08762_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08762 (fullRecordGapValue08762 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08762_not_prime : ¬(recordGapCenter + 524562).Prime := by
  rw [fullRecordGapTerm08762_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08762, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08762_fast_pow_mod_ne_one

def fullRecordGapValue08763 : Nat := fullRecordGapCenterValue + 524598

theorem fullRecordGapTerm08763_eq_value :
    recordGapCenter + 524598 = fullRecordGapValue08763 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08763_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08763 (fullRecordGapValue08763 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08763_not_prime : ¬(recordGapCenter + 524598).Prime := by
  rw [fullRecordGapTerm08763_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08763, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08763_fast_pow_mod_ne_one

def fullRecordGapValue08764 : Nat := fullRecordGapCenterValue + 524658

theorem fullRecordGapTerm08764_eq_value :
    recordGapCenter + 524658 = fullRecordGapValue08764 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08764_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08764 (fullRecordGapValue08764 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08764_not_prime : ¬(recordGapCenter + 524658).Prime := by
  rw [fullRecordGapTerm08764_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08764, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08764_fast_pow_mod_ne_one

def fullRecordGapValue08765 : Nat := fullRecordGapCenterValue + 524738

theorem fullRecordGapTerm08765_eq_value :
    recordGapCenter + 524738 = fullRecordGapValue08765 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08765_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08765 (fullRecordGapValue08765 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08765_not_prime : ¬(recordGapCenter + 524738).Prime := by
  rw [fullRecordGapTerm08765_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08765, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08765_fast_pow_mod_ne_one

def fullRecordGapValue08766 : Nat := fullRecordGapCenterValue + 524918

theorem fullRecordGapTerm08766_eq_value :
    recordGapCenter + 524918 = fullRecordGapValue08766 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08766_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08766 (fullRecordGapValue08766 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08766_not_prime : ¬(recordGapCenter + 524918).Prime := by
  rw [fullRecordGapTerm08766_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08766, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08766_fast_pow_mod_ne_one

def fullRecordGapValue08767 : Nat := fullRecordGapCenterValue + 524996

theorem fullRecordGapTerm08767_eq_value :
    recordGapCenter + 524996 = fullRecordGapValue08767 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08767_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08767 (fullRecordGapValue08767 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08767_not_prime : ¬(recordGapCenter + 524996).Prime := by
  rw [fullRecordGapTerm08767_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08767, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08767_fast_pow_mod_ne_one

def fullRecordGapValue08768 : Nat := fullRecordGapCenterValue + 525036

theorem fullRecordGapTerm08768_eq_value :
    recordGapCenter + 525036 = fullRecordGapValue08768 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08768_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08768 (fullRecordGapValue08768 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08768_not_prime : ¬(recordGapCenter + 525036).Prime := by
  rw [fullRecordGapTerm08768_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08768, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08768_fast_pow_mod_ne_one

def fullRecordGapValue08769 : Nat := fullRecordGapCenterValue + 525038

theorem fullRecordGapTerm08769_eq_value :
    recordGapCenter + 525038 = fullRecordGapValue08769 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08769_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08769 (fullRecordGapValue08769 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08769_not_prime : ¬(recordGapCenter + 525038).Prime := by
  rw [fullRecordGapTerm08769_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08769, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08769_fast_pow_mod_ne_one

def fullRecordGapValue08770 : Nat := fullRecordGapCenterValue + 525068

theorem fullRecordGapTerm08770_eq_value :
    recordGapCenter + 525068 = fullRecordGapValue08770 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08770_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08770 (fullRecordGapValue08770 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08770_not_prime : ¬(recordGapCenter + 525068).Prime := by
  rw [fullRecordGapTerm08770_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08770, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08770_fast_pow_mod_ne_one

def fullRecordGapValue08771 : Nat := fullRecordGapCenterValue + 525102

theorem fullRecordGapTerm08771_eq_value :
    recordGapCenter + 525102 = fullRecordGapValue08771 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08771_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08771 (fullRecordGapValue08771 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08771_not_prime : ¬(recordGapCenter + 525102).Prime := by
  rw [fullRecordGapTerm08771_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08771, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08771_fast_pow_mod_ne_one

def fullRecordGapValue08772 : Nat := fullRecordGapCenterValue + 525108

theorem fullRecordGapTerm08772_eq_value :
    recordGapCenter + 525108 = fullRecordGapValue08772 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08772_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08772 (fullRecordGapValue08772 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08772_not_prime : ¬(recordGapCenter + 525108).Prime := by
  rw [fullRecordGapTerm08772_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08772, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08772_fast_pow_mod_ne_one

def fullRecordGapValue08773 : Nat := fullRecordGapCenterValue + 525110

theorem fullRecordGapTerm08773_eq_value :
    recordGapCenter + 525110 = fullRecordGapValue08773 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08773_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08773 (fullRecordGapValue08773 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08773_not_prime : ¬(recordGapCenter + 525110).Prime := by
  rw [fullRecordGapTerm08773_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08773, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08773_fast_pow_mod_ne_one

def fullRecordGapValue08774 : Nat := fullRecordGapCenterValue + 525138

theorem fullRecordGapTerm08774_eq_value :
    recordGapCenter + 525138 = fullRecordGapValue08774 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08774_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08774 (fullRecordGapValue08774 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08774_not_prime : ¬(recordGapCenter + 525138).Prime := by
  rw [fullRecordGapTerm08774_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08774, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08774_fast_pow_mod_ne_one

def fullRecordGapValue08775 : Nat := fullRecordGapCenterValue + 525170

theorem fullRecordGapTerm08775_eq_value :
    recordGapCenter + 525170 = fullRecordGapValue08775 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08775_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08775 (fullRecordGapValue08775 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08775_not_prime : ¬(recordGapCenter + 525170).Prime := by
  rw [fullRecordGapTerm08775_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08775, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08775_fast_pow_mod_ne_one

def fullRecordGapValue08776 : Nat := fullRecordGapCenterValue + 525176

theorem fullRecordGapTerm08776_eq_value :
    recordGapCenter + 525176 = fullRecordGapValue08776 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08776_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08776 (fullRecordGapValue08776 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08776_not_prime : ¬(recordGapCenter + 525176).Prime := by
  rw [fullRecordGapTerm08776_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08776, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08776_fast_pow_mod_ne_one

def fullRecordGapValue08777 : Nat := fullRecordGapCenterValue + 525282

theorem fullRecordGapTerm08777_eq_value :
    recordGapCenter + 525282 = fullRecordGapValue08777 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08777_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08777 (fullRecordGapValue08777 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08777_not_prime : ¬(recordGapCenter + 525282).Prime := by
  rw [fullRecordGapTerm08777_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08777, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08777_fast_pow_mod_ne_one

def fullRecordGapValue08778 : Nat := fullRecordGapCenterValue + 525302

theorem fullRecordGapTerm08778_eq_value :
    recordGapCenter + 525302 = fullRecordGapValue08778 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08778_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08778 (fullRecordGapValue08778 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08778_not_prime : ¬(recordGapCenter + 525302).Prime := by
  rw [fullRecordGapTerm08778_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08778, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08778_fast_pow_mod_ne_one

def fullRecordGapValue08779 : Nat := fullRecordGapCenterValue + 525318

theorem fullRecordGapTerm08779_eq_value :
    recordGapCenter + 525318 = fullRecordGapValue08779 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08779_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08779 (fullRecordGapValue08779 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08779_not_prime : ¬(recordGapCenter + 525318).Prime := by
  rw [fullRecordGapTerm08779_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08779, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08779_fast_pow_mod_ne_one

def fullRecordGapValue08780 : Nat := fullRecordGapCenterValue + 525362

theorem fullRecordGapTerm08780_eq_value :
    recordGapCenter + 525362 = fullRecordGapValue08780 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08780_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08780 (fullRecordGapValue08780 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08780_not_prime : ¬(recordGapCenter + 525362).Prime := by
  rw [fullRecordGapTerm08780_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08780, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08780_fast_pow_mod_ne_one

def fullRecordGapValue08781 : Nat := fullRecordGapCenterValue + 525372

theorem fullRecordGapTerm08781_eq_value :
    recordGapCenter + 525372 = fullRecordGapValue08781 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08781_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08781 (fullRecordGapValue08781 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08781_not_prime : ¬(recordGapCenter + 525372).Prime := by
  rw [fullRecordGapTerm08781_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08781, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08781_fast_pow_mod_ne_one

def fullRecordGapValue08782 : Nat := fullRecordGapCenterValue + 525386

theorem fullRecordGapTerm08782_eq_value :
    recordGapCenter + 525386 = fullRecordGapValue08782 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08782_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08782 (fullRecordGapValue08782 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08782_not_prime : ¬(recordGapCenter + 525386).Prime := by
  rw [fullRecordGapTerm08782_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08782, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08782_fast_pow_mod_ne_one

def fullRecordGapValue08783 : Nat := fullRecordGapCenterValue + 525396

theorem fullRecordGapTerm08783_eq_value :
    recordGapCenter + 525396 = fullRecordGapValue08783 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08783_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08783 (fullRecordGapValue08783 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08783_not_prime : ¬(recordGapCenter + 525396).Prime := by
  rw [fullRecordGapTerm08783_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08783, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08783_fast_pow_mod_ne_one

def fullRecordGapValue08784 : Nat := fullRecordGapCenterValue + 525410

theorem fullRecordGapTerm08784_eq_value :
    recordGapCenter + 525410 = fullRecordGapValue08784 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08784_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08784 (fullRecordGapValue08784 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08784_not_prime : ¬(recordGapCenter + 525410).Prime := by
  rw [fullRecordGapTerm08784_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08784, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08784_fast_pow_mod_ne_one

def fullRecordGapValue08785 : Nat := fullRecordGapCenterValue + 525446

theorem fullRecordGapTerm08785_eq_value :
    recordGapCenter + 525446 = fullRecordGapValue08785 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08785_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08785 (fullRecordGapValue08785 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08785_not_prime : ¬(recordGapCenter + 525446).Prime := by
  rw [fullRecordGapTerm08785_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08785, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08785_fast_pow_mod_ne_one

def fullRecordGapValue08786 : Nat := fullRecordGapCenterValue + 525452

theorem fullRecordGapTerm08786_eq_value :
    recordGapCenter + 525452 = fullRecordGapValue08786 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08786_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08786 (fullRecordGapValue08786 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08786_not_prime : ¬(recordGapCenter + 525452).Prime := by
  rw [fullRecordGapTerm08786_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08786, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08786_fast_pow_mod_ne_one

def fullRecordGapValue08787 : Nat := fullRecordGapCenterValue + 525498

theorem fullRecordGapTerm08787_eq_value :
    recordGapCenter + 525498 = fullRecordGapValue08787 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08787_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08787 (fullRecordGapValue08787 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08787_not_prime : ¬(recordGapCenter + 525498).Prime := by
  rw [fullRecordGapTerm08787_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08787, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08787_fast_pow_mod_ne_one

def fullRecordGapValue08788 : Nat := fullRecordGapCenterValue + 525612

theorem fullRecordGapTerm08788_eq_value :
    recordGapCenter + 525612 = fullRecordGapValue08788 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08788_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08788 (fullRecordGapValue08788 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08788_not_prime : ¬(recordGapCenter + 525612).Prime := by
  rw [fullRecordGapTerm08788_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08788, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08788_fast_pow_mod_ne_one

def fullRecordGapValue08789 : Nat := fullRecordGapCenterValue + 525656

theorem fullRecordGapTerm08789_eq_value :
    recordGapCenter + 525656 = fullRecordGapValue08789 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08789_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08789 (fullRecordGapValue08789 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08789_not_prime : ¬(recordGapCenter + 525656).Prime := by
  rw [fullRecordGapTerm08789_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08789, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08789_fast_pow_mod_ne_one

def fullRecordGapValue08790 : Nat := fullRecordGapCenterValue + 525738

theorem fullRecordGapTerm08790_eq_value :
    recordGapCenter + 525738 = fullRecordGapValue08790 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08790_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08790 (fullRecordGapValue08790 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08790_not_prime : ¬(recordGapCenter + 525738).Prime := by
  rw [fullRecordGapTerm08790_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08790, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08790_fast_pow_mod_ne_one

def fullRecordGapValue08791 : Nat := fullRecordGapCenterValue + 525786

theorem fullRecordGapTerm08791_eq_value :
    recordGapCenter + 525786 = fullRecordGapValue08791 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08791_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08791 (fullRecordGapValue08791 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08791_not_prime : ¬(recordGapCenter + 525786).Prime := by
  rw [fullRecordGapTerm08791_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08791, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08791_fast_pow_mod_ne_one

def fullRecordGapValue08792 : Nat := fullRecordGapCenterValue + 525788

theorem fullRecordGapTerm08792_eq_value :
    recordGapCenter + 525788 = fullRecordGapValue08792 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08792_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08792 (fullRecordGapValue08792 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08792_not_prime : ¬(recordGapCenter + 525788).Prime := by
  rw [fullRecordGapTerm08792_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08792, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08792_fast_pow_mod_ne_one

def fullRecordGapValue08793 : Nat := fullRecordGapCenterValue + 525830

theorem fullRecordGapTerm08793_eq_value :
    recordGapCenter + 525830 = fullRecordGapValue08793 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08793_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08793 (fullRecordGapValue08793 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08793_not_prime : ¬(recordGapCenter + 525830).Prime := by
  rw [fullRecordGapTerm08793_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08793, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08793_fast_pow_mod_ne_one

def fullRecordGapValue08794 : Nat := fullRecordGapCenterValue + 525848

theorem fullRecordGapTerm08794_eq_value :
    recordGapCenter + 525848 = fullRecordGapValue08794 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08794_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08794 (fullRecordGapValue08794 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08794_not_prime : ¬(recordGapCenter + 525848).Prime := by
  rw [fullRecordGapTerm08794_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08794, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08794_fast_pow_mod_ne_one

def fullRecordGapValue08795 : Nat := fullRecordGapCenterValue + 525956

theorem fullRecordGapTerm08795_eq_value :
    recordGapCenter + 525956 = fullRecordGapValue08795 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08795_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08795 (fullRecordGapValue08795 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08795_not_prime : ¬(recordGapCenter + 525956).Prime := by
  rw [fullRecordGapTerm08795_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08795, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08795_fast_pow_mod_ne_one

def fullRecordGapValue08796 : Nat := fullRecordGapCenterValue + 526088

theorem fullRecordGapTerm08796_eq_value :
    recordGapCenter + 526088 = fullRecordGapValue08796 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08796_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08796 (fullRecordGapValue08796 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08796_not_prime : ¬(recordGapCenter + 526088).Prime := by
  rw [fullRecordGapTerm08796_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08796, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08796_fast_pow_mod_ne_one

def fullRecordGapValue08797 : Nat := fullRecordGapCenterValue + 526142

theorem fullRecordGapTerm08797_eq_value :
    recordGapCenter + 526142 = fullRecordGapValue08797 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08797_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08797 (fullRecordGapValue08797 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08797_not_prime : ¬(recordGapCenter + 526142).Prime := by
  rw [fullRecordGapTerm08797_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08797, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08797_fast_pow_mod_ne_one

def fullRecordGapValue08798 : Nat := fullRecordGapCenterValue + 526146

theorem fullRecordGapTerm08798_eq_value :
    recordGapCenter + 526146 = fullRecordGapValue08798 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08798_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08798 (fullRecordGapValue08798 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08798_not_prime : ¬(recordGapCenter + 526146).Prime := by
  rw [fullRecordGapTerm08798_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08798, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08798_fast_pow_mod_ne_one

def fullRecordGapValue08799 : Nat := fullRecordGapCenterValue + 526206

theorem fullRecordGapTerm08799_eq_value :
    recordGapCenter + 526206 = fullRecordGapValue08799 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08799_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08799 (fullRecordGapValue08799 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08799_not_prime : ¬(recordGapCenter + 526206).Prime := by
  rw [fullRecordGapTerm08799_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08799, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08799_fast_pow_mod_ne_one

def fullRecordGapValue08800 : Nat := fullRecordGapCenterValue + 526418

theorem fullRecordGapTerm08800_eq_value :
    recordGapCenter + 526418 = fullRecordGapValue08800 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08800_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08800 (fullRecordGapValue08800 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08800_not_prime : ¬(recordGapCenter + 526418).Prime := by
  rw [fullRecordGapTerm08800_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08800, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08800_fast_pow_mod_ne_one

def fullRecordGapValue08801 : Nat := fullRecordGapCenterValue + 526472

theorem fullRecordGapTerm08801_eq_value :
    recordGapCenter + 526472 = fullRecordGapValue08801 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08801_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08801 (fullRecordGapValue08801 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08801_not_prime : ¬(recordGapCenter + 526472).Prime := by
  rw [fullRecordGapTerm08801_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08801, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08801_fast_pow_mod_ne_one

def fullRecordGapValue08802 : Nat := fullRecordGapCenterValue + 526646

theorem fullRecordGapTerm08802_eq_value :
    recordGapCenter + 526646 = fullRecordGapValue08802 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08802_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08802 (fullRecordGapValue08802 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08802_not_prime : ¬(recordGapCenter + 526646).Prime := by
  rw [fullRecordGapTerm08802_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08802, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08802_fast_pow_mod_ne_one

def fullRecordGapValue08803 : Nat := fullRecordGapCenterValue + 526670

theorem fullRecordGapTerm08803_eq_value :
    recordGapCenter + 526670 = fullRecordGapValue08803 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08803_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08803 (fullRecordGapValue08803 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08803_not_prime : ¬(recordGapCenter + 526670).Prime := by
  rw [fullRecordGapTerm08803_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08803, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08803_fast_pow_mod_ne_one

def fullRecordGapValue08804 : Nat := fullRecordGapCenterValue + 526692

theorem fullRecordGapTerm08804_eq_value :
    recordGapCenter + 526692 = fullRecordGapValue08804 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08804_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08804 (fullRecordGapValue08804 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08804_not_prime : ¬(recordGapCenter + 526692).Prime := by
  rw [fullRecordGapTerm08804_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08804, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08804_fast_pow_mod_ne_one

def fullRecordGapValue08805 : Nat := fullRecordGapCenterValue + 526712

theorem fullRecordGapTerm08805_eq_value :
    recordGapCenter + 526712 = fullRecordGapValue08805 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08805_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08805 (fullRecordGapValue08805 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08805_not_prime : ¬(recordGapCenter + 526712).Prime := by
  rw [fullRecordGapTerm08805_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08805, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08805_fast_pow_mod_ne_one

def fullRecordGapValue08806 : Nat := fullRecordGapCenterValue + 526730

theorem fullRecordGapTerm08806_eq_value :
    recordGapCenter + 526730 = fullRecordGapValue08806 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08806_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08806 (fullRecordGapValue08806 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08806_not_prime : ¬(recordGapCenter + 526730).Prime := by
  rw [fullRecordGapTerm08806_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08806, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08806_fast_pow_mod_ne_one

def fullRecordGapValue08807 : Nat := fullRecordGapCenterValue + 526766

theorem fullRecordGapTerm08807_eq_value :
    recordGapCenter + 526766 = fullRecordGapValue08807 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08807_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08807 (fullRecordGapValue08807 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08807_not_prime : ¬(recordGapCenter + 526766).Prime := by
  rw [fullRecordGapTerm08807_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08807, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08807_fast_pow_mod_ne_one

def fullRecordGapValue08808 : Nat := fullRecordGapCenterValue + 526818

theorem fullRecordGapTerm08808_eq_value :
    recordGapCenter + 526818 = fullRecordGapValue08808 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08808_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08808 (fullRecordGapValue08808 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08808_not_prime : ¬(recordGapCenter + 526818).Prime := by
  rw [fullRecordGapTerm08808_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08808, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08808_fast_pow_mod_ne_one

def fullRecordGapValue08809 : Nat := fullRecordGapCenterValue + 526848

theorem fullRecordGapTerm08809_eq_value :
    recordGapCenter + 526848 = fullRecordGapValue08809 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08809_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08809 (fullRecordGapValue08809 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08809_not_prime : ¬(recordGapCenter + 526848).Prime := by
  rw [fullRecordGapTerm08809_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08809, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08809_fast_pow_mod_ne_one

def fullRecordGapValue08810 : Nat := fullRecordGapCenterValue + 527066

theorem fullRecordGapTerm08810_eq_value :
    recordGapCenter + 527066 = fullRecordGapValue08810 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08810_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08810 (fullRecordGapValue08810 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08810_not_prime : ¬(recordGapCenter + 527066).Prime := by
  rw [fullRecordGapTerm08810_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08810, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08810_fast_pow_mod_ne_one

def fullRecordGapValue08811 : Nat := fullRecordGapCenterValue + 527090

theorem fullRecordGapTerm08811_eq_value :
    recordGapCenter + 527090 = fullRecordGapValue08811 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08811_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08811 (fullRecordGapValue08811 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08811_not_prime : ¬(recordGapCenter + 527090).Prime := by
  rw [fullRecordGapTerm08811_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08811, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08811_fast_pow_mod_ne_one

def fullRecordGapValue08812 : Nat := fullRecordGapCenterValue + 527210

theorem fullRecordGapTerm08812_eq_value :
    recordGapCenter + 527210 = fullRecordGapValue08812 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08812_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08812 (fullRecordGapValue08812 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08812_not_prime : ¬(recordGapCenter + 527210).Prime := by
  rw [fullRecordGapTerm08812_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08812, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08812_fast_pow_mod_ne_one

def fullRecordGapValue08813 : Nat := fullRecordGapCenterValue + 527222

theorem fullRecordGapTerm08813_eq_value :
    recordGapCenter + 527222 = fullRecordGapValue08813 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08813_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08813 (fullRecordGapValue08813 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08813_not_prime : ¬(recordGapCenter + 527222).Prime := by
  rw [fullRecordGapTerm08813_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08813, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08813_fast_pow_mod_ne_one

def fullRecordGapValue08814 : Nat := fullRecordGapCenterValue + 527286

theorem fullRecordGapTerm08814_eq_value :
    recordGapCenter + 527286 = fullRecordGapValue08814 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08814_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08814 (fullRecordGapValue08814 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08814_not_prime : ¬(recordGapCenter + 527286).Prime := by
  rw [fullRecordGapTerm08814_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08814, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08814_fast_pow_mod_ne_one

def fullRecordGapValue08815 : Nat := fullRecordGapCenterValue + 527348

theorem fullRecordGapTerm08815_eq_value :
    recordGapCenter + 527348 = fullRecordGapValue08815 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08815_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08815 (fullRecordGapValue08815 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08815_not_prime : ¬(recordGapCenter + 527348).Prime := by
  rw [fullRecordGapTerm08815_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08815, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08815_fast_pow_mod_ne_one

def fullRecordGapValue08816 : Nat := fullRecordGapCenterValue + 527396

theorem fullRecordGapTerm08816_eq_value :
    recordGapCenter + 527396 = fullRecordGapValue08816 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08816_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08816 (fullRecordGapValue08816 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08816_not_prime : ¬(recordGapCenter + 527396).Prime := by
  rw [fullRecordGapTerm08816_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08816, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08816_fast_pow_mod_ne_one

def fullRecordGapValue08817 : Nat := fullRecordGapCenterValue + 527570

theorem fullRecordGapTerm08817_eq_value :
    recordGapCenter + 527570 = fullRecordGapValue08817 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08817_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08817 (fullRecordGapValue08817 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08817_not_prime : ¬(recordGapCenter + 527570).Prime := by
  rw [fullRecordGapTerm08817_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08817, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08817_fast_pow_mod_ne_one

def fullRecordGapValue08818 : Nat := fullRecordGapCenterValue + 527636

theorem fullRecordGapTerm08818_eq_value :
    recordGapCenter + 527636 = fullRecordGapValue08818 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08818_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08818 (fullRecordGapValue08818 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08818_not_prime : ¬(recordGapCenter + 527636).Prime := by
  rw [fullRecordGapTerm08818_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08818, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08818_fast_pow_mod_ne_one

def fullRecordGapValue08819 : Nat := fullRecordGapCenterValue + 527658

theorem fullRecordGapTerm08819_eq_value :
    recordGapCenter + 527658 = fullRecordGapValue08819 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08819_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08819 (fullRecordGapValue08819 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08819_not_prime : ¬(recordGapCenter + 527658).Prime := by
  rw [fullRecordGapTerm08819_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08819, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08819_fast_pow_mod_ne_one

def fullRecordGapValue08820 : Nat := fullRecordGapCenterValue + 527676

theorem fullRecordGapTerm08820_eq_value :
    recordGapCenter + 527676 = fullRecordGapValue08820 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08820_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08820 (fullRecordGapValue08820 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08820_not_prime : ¬(recordGapCenter + 527676).Prime := by
  rw [fullRecordGapTerm08820_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08820, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08820_fast_pow_mod_ne_one

def fullRecordGapValue08821 : Nat := fullRecordGapCenterValue + 527726

theorem fullRecordGapTerm08821_eq_value :
    recordGapCenter + 527726 = fullRecordGapValue08821 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08821_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08821 (fullRecordGapValue08821 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08821_not_prime : ¬(recordGapCenter + 527726).Prime := by
  rw [fullRecordGapTerm08821_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08821, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08821_fast_pow_mod_ne_one

def fullRecordGapValue08822 : Nat := fullRecordGapCenterValue + 527756

theorem fullRecordGapTerm08822_eq_value :
    recordGapCenter + 527756 = fullRecordGapValue08822 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08822_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08822 (fullRecordGapValue08822 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08822_not_prime : ¬(recordGapCenter + 527756).Prime := by
  rw [fullRecordGapTerm08822_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08822, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08822_fast_pow_mod_ne_one

def fullRecordGapValue08823 : Nat := fullRecordGapCenterValue + 527762

theorem fullRecordGapTerm08823_eq_value :
    recordGapCenter + 527762 = fullRecordGapValue08823 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08823_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08823 (fullRecordGapValue08823 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08823_not_prime : ¬(recordGapCenter + 527762).Prime := by
  rw [fullRecordGapTerm08823_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08823, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08823_fast_pow_mod_ne_one

def fullRecordGapValue08824 : Nat := fullRecordGapCenterValue + 527838

theorem fullRecordGapTerm08824_eq_value :
    recordGapCenter + 527838 = fullRecordGapValue08824 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08824_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08824 (fullRecordGapValue08824 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08824_not_prime : ¬(recordGapCenter + 527838).Prime := by
  rw [fullRecordGapTerm08824_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08824, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08824_fast_pow_mod_ne_one

def fullRecordGapValue08825 : Nat := fullRecordGapCenterValue + 527882

theorem fullRecordGapTerm08825_eq_value :
    recordGapCenter + 527882 = fullRecordGapValue08825 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08825_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08825 (fullRecordGapValue08825 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08825_not_prime : ¬(recordGapCenter + 527882).Prime := by
  rw [fullRecordGapTerm08825_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08825, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08825_fast_pow_mod_ne_one

def fullRecordGapValue08826 : Nat := fullRecordGapCenterValue + 527892

theorem fullRecordGapTerm08826_eq_value :
    recordGapCenter + 527892 = fullRecordGapValue08826 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08826_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08826 (fullRecordGapValue08826 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08826_not_prime : ¬(recordGapCenter + 527892).Prime := by
  rw [fullRecordGapTerm08826_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08826, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08826_fast_pow_mod_ne_one

def fullRecordGapValue08827 : Nat := fullRecordGapCenterValue + 527966

theorem fullRecordGapTerm08827_eq_value :
    recordGapCenter + 527966 = fullRecordGapValue08827 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08827_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08827 (fullRecordGapValue08827 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08827_not_prime : ¬(recordGapCenter + 527966).Prime := by
  rw [fullRecordGapTerm08827_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08827, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08827_fast_pow_mod_ne_one

def fullRecordGapValue08828 : Nat := fullRecordGapCenterValue + 528000

theorem fullRecordGapTerm08828_eq_value :
    recordGapCenter + 528000 = fullRecordGapValue08828 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08828_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08828 (fullRecordGapValue08828 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08828_not_prime : ¬(recordGapCenter + 528000).Prime := by
  rw [fullRecordGapTerm08828_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08828, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08828_fast_pow_mod_ne_one

def fullRecordGapValue08829 : Nat := fullRecordGapCenterValue + 528006

theorem fullRecordGapTerm08829_eq_value :
    recordGapCenter + 528006 = fullRecordGapValue08829 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08829_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08829 (fullRecordGapValue08829 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08829_not_prime : ¬(recordGapCenter + 528006).Prime := by
  rw [fullRecordGapTerm08829_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08829, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08829_fast_pow_mod_ne_one

def fullRecordGapValue08830 : Nat := fullRecordGapCenterValue + 528182

theorem fullRecordGapTerm08830_eq_value :
    recordGapCenter + 528182 = fullRecordGapValue08830 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08830_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08830 (fullRecordGapValue08830 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08830_not_prime : ¬(recordGapCenter + 528182).Prime := by
  rw [fullRecordGapTerm08830_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08830, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08830_fast_pow_mod_ne_one

def fullRecordGapValue08831 : Nat := fullRecordGapCenterValue + 528188

theorem fullRecordGapTerm08831_eq_value :
    recordGapCenter + 528188 = fullRecordGapValue08831 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08831_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08831 (fullRecordGapValue08831 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08831_not_prime : ¬(recordGapCenter + 528188).Prime := by
  rw [fullRecordGapTerm08831_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08831, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08831_fast_pow_mod_ne_one

def fullRecordGapValue08832 : Nat := fullRecordGapCenterValue + 528252

theorem fullRecordGapTerm08832_eq_value :
    recordGapCenter + 528252 = fullRecordGapValue08832 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08832_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08832 (fullRecordGapValue08832 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08832_not_prime : ¬(recordGapCenter + 528252).Prime := by
  rw [fullRecordGapTerm08832_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08832, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08832_fast_pow_mod_ne_one

def fullRecordGapValue08833 : Nat := fullRecordGapCenterValue + 528278

theorem fullRecordGapTerm08833_eq_value :
    recordGapCenter + 528278 = fullRecordGapValue08833 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08833_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08833 (fullRecordGapValue08833 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08833_not_prime : ¬(recordGapCenter + 528278).Prime := by
  rw [fullRecordGapTerm08833_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08833, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08833_fast_pow_mod_ne_one

def fullRecordGapValue08834 : Nat := fullRecordGapCenterValue + 528566

theorem fullRecordGapTerm08834_eq_value :
    recordGapCenter + 528566 = fullRecordGapValue08834 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08834_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08834 (fullRecordGapValue08834 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08834_not_prime : ¬(recordGapCenter + 528566).Prime := by
  rw [fullRecordGapTerm08834_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08834, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08834_fast_pow_mod_ne_one

def fullRecordGapValue08835 : Nat := fullRecordGapCenterValue + 528662

theorem fullRecordGapTerm08835_eq_value :
    recordGapCenter + 528662 = fullRecordGapValue08835 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08835_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08835 (fullRecordGapValue08835 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08835_not_prime : ¬(recordGapCenter + 528662).Prime := by
  rw [fullRecordGapTerm08835_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08835, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08835_fast_pow_mod_ne_one

def fullRecordGapValue08836 : Nat := fullRecordGapCenterValue + 528698

theorem fullRecordGapTerm08836_eq_value :
    recordGapCenter + 528698 = fullRecordGapValue08836 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08836_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08836 (fullRecordGapValue08836 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08836_not_prime : ¬(recordGapCenter + 528698).Prime := by
  rw [fullRecordGapTerm08836_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08836, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08836_fast_pow_mod_ne_one

def fullRecordGapValue08837 : Nat := fullRecordGapCenterValue + 528872

theorem fullRecordGapTerm08837_eq_value :
    recordGapCenter + 528872 = fullRecordGapValue08837 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08837_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08837 (fullRecordGapValue08837 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08837_not_prime : ¬(recordGapCenter + 528872).Prime := by
  rw [fullRecordGapTerm08837_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08837, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08837_fast_pow_mod_ne_one

def fullRecordGapValue08838 : Nat := fullRecordGapCenterValue + 529062

theorem fullRecordGapTerm08838_eq_value :
    recordGapCenter + 529062 = fullRecordGapValue08838 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08838_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08838 (fullRecordGapValue08838 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08838_not_prime : ¬(recordGapCenter + 529062).Prime := by
  rw [fullRecordGapTerm08838_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08838, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08838_fast_pow_mod_ne_one

def fullRecordGapValue08839 : Nat := fullRecordGapCenterValue + 529106

theorem fullRecordGapTerm08839_eq_value :
    recordGapCenter + 529106 = fullRecordGapValue08839 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08839_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08839 (fullRecordGapValue08839 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08839_not_prime : ¬(recordGapCenter + 529106).Prime := by
  rw [fullRecordGapTerm08839_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08839, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08839_fast_pow_mod_ne_one

def fullRecordGapValue08840 : Nat := fullRecordGapCenterValue + 529190

theorem fullRecordGapTerm08840_eq_value :
    recordGapCenter + 529190 = fullRecordGapValue08840 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08840_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08840 (fullRecordGapValue08840 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08840_not_prime : ¬(recordGapCenter + 529190).Prime := by
  rw [fullRecordGapTerm08840_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08840, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08840_fast_pow_mod_ne_one

def fullRecordGapValue08841 : Nat := fullRecordGapCenterValue + 529200

theorem fullRecordGapTerm08841_eq_value :
    recordGapCenter + 529200 = fullRecordGapValue08841 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08841_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08841 (fullRecordGapValue08841 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08841_not_prime : ¬(recordGapCenter + 529200).Prime := by
  rw [fullRecordGapTerm08841_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08841, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08841_fast_pow_mod_ne_one

def fullRecordGapValue08842 : Nat := fullRecordGapCenterValue + 529212

theorem fullRecordGapTerm08842_eq_value :
    recordGapCenter + 529212 = fullRecordGapValue08842 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08842_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08842 (fullRecordGapValue08842 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08842_not_prime : ¬(recordGapCenter + 529212).Prime := by
  rw [fullRecordGapTerm08842_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08842, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08842_fast_pow_mod_ne_one

def fullRecordGapValue08843 : Nat := fullRecordGapCenterValue + 529422

theorem fullRecordGapTerm08843_eq_value :
    recordGapCenter + 529422 = fullRecordGapValue08843 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08843_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08843 (fullRecordGapValue08843 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08843_not_prime : ¬(recordGapCenter + 529422).Prime := by
  rw [fullRecordGapTerm08843_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08843, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08843_fast_pow_mod_ne_one

def fullRecordGapValue08844 : Nat := fullRecordGapCenterValue + 529428

theorem fullRecordGapTerm08844_eq_value :
    recordGapCenter + 529428 = fullRecordGapValue08844 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08844_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08844 (fullRecordGapValue08844 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08844_not_prime : ¬(recordGapCenter + 529428).Prime := by
  rw [fullRecordGapTerm08844_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08844, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08844_fast_pow_mod_ne_one

def fullRecordGapValue08845 : Nat := fullRecordGapCenterValue + 529446

theorem fullRecordGapTerm08845_eq_value :
    recordGapCenter + 529446 = fullRecordGapValue08845 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08845_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08845 (fullRecordGapValue08845 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08845_not_prime : ¬(recordGapCenter + 529446).Prime := by
  rw [fullRecordGapTerm08845_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08845, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08845_fast_pow_mod_ne_one

def fullRecordGapValue08846 : Nat := fullRecordGapCenterValue + 529526

theorem fullRecordGapTerm08846_eq_value :
    recordGapCenter + 529526 = fullRecordGapValue08846 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08846_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08846 (fullRecordGapValue08846 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08846_not_prime : ¬(recordGapCenter + 529526).Prime := by
  rw [fullRecordGapTerm08846_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08846, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08846_fast_pow_mod_ne_one

def fullRecordGapValue08847 : Nat := fullRecordGapCenterValue + 529548

theorem fullRecordGapTerm08847_eq_value :
    recordGapCenter + 529548 = fullRecordGapValue08847 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08847_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08847 (fullRecordGapValue08847 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08847_not_prime : ¬(recordGapCenter + 529548).Prime := by
  rw [fullRecordGapTerm08847_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08847, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08847_fast_pow_mod_ne_one

def fullRecordGapValue08848 : Nat := fullRecordGapCenterValue + 529566

theorem fullRecordGapTerm08848_eq_value :
    recordGapCenter + 529566 = fullRecordGapValue08848 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08848_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08848 (fullRecordGapValue08848 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08848_not_prime : ¬(recordGapCenter + 529566).Prime := by
  rw [fullRecordGapTerm08848_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08848, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08848_fast_pow_mod_ne_one

def fullRecordGapValue08849 : Nat := fullRecordGapCenterValue + 529572

theorem fullRecordGapTerm08849_eq_value :
    recordGapCenter + 529572 = fullRecordGapValue08849 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08849_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08849 (fullRecordGapValue08849 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08849_not_prime : ¬(recordGapCenter + 529572).Prime := by
  rw [fullRecordGapTerm08849_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08849, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08849_fast_pow_mod_ne_one

def fullRecordGapValue08850 : Nat := fullRecordGapCenterValue + 529658

theorem fullRecordGapTerm08850_eq_value :
    recordGapCenter + 529658 = fullRecordGapValue08850 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08850_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08850 (fullRecordGapValue08850 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08850_not_prime : ¬(recordGapCenter + 529658).Prime := by
  rw [fullRecordGapTerm08850_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08850, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08850_fast_pow_mod_ne_one

def fullRecordGapValue08851 : Nat := fullRecordGapCenterValue + 529730

theorem fullRecordGapTerm08851_eq_value :
    recordGapCenter + 529730 = fullRecordGapValue08851 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08851_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08851 (fullRecordGapValue08851 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08851_not_prime : ¬(recordGapCenter + 529730).Prime := by
  rw [fullRecordGapTerm08851_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08851, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08851_fast_pow_mod_ne_one

def fullRecordGapValue08852 : Nat := fullRecordGapCenterValue + 529742

theorem fullRecordGapTerm08852_eq_value :
    recordGapCenter + 529742 = fullRecordGapValue08852 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08852_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08852 (fullRecordGapValue08852 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08852_not_prime : ¬(recordGapCenter + 529742).Prime := by
  rw [fullRecordGapTerm08852_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08852, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08852_fast_pow_mod_ne_one

def fullRecordGapValue08853 : Nat := fullRecordGapCenterValue + 529748

theorem fullRecordGapTerm08853_eq_value :
    recordGapCenter + 529748 = fullRecordGapValue08853 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08853_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08853 (fullRecordGapValue08853 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08853_not_prime : ¬(recordGapCenter + 529748).Prime := by
  rw [fullRecordGapTerm08853_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08853, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08853_fast_pow_mod_ne_one

def fullRecordGapValue08854 : Nat := fullRecordGapCenterValue + 529862

theorem fullRecordGapTerm08854_eq_value :
    recordGapCenter + 529862 = fullRecordGapValue08854 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08854_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08854 (fullRecordGapValue08854 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08854_not_prime : ¬(recordGapCenter + 529862).Prime := by
  rw [fullRecordGapTerm08854_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08854, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08854_fast_pow_mod_ne_one

def fullRecordGapValue08855 : Nat := fullRecordGapCenterValue + 529898

theorem fullRecordGapTerm08855_eq_value :
    recordGapCenter + 529898 = fullRecordGapValue08855 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08855_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08855 (fullRecordGapValue08855 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08855_not_prime : ¬(recordGapCenter + 529898).Prime := by
  rw [fullRecordGapTerm08855_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08855, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08855_fast_pow_mod_ne_one

def fullRecordGapValue08856 : Nat := fullRecordGapCenterValue + 529908

theorem fullRecordGapTerm08856_eq_value :
    recordGapCenter + 529908 = fullRecordGapValue08856 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08856_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08856 (fullRecordGapValue08856 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08856_not_prime : ¬(recordGapCenter + 529908).Prime := by
  rw [fullRecordGapTerm08856_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08856, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08856_fast_pow_mod_ne_one

def fullRecordGapValue08857 : Nat := fullRecordGapCenterValue + 529926

theorem fullRecordGapTerm08857_eq_value :
    recordGapCenter + 529926 = fullRecordGapValue08857 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08857_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08857 (fullRecordGapValue08857 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08857_not_prime : ¬(recordGapCenter + 529926).Prime := by
  rw [fullRecordGapTerm08857_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08857, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08857_fast_pow_mod_ne_one

def fullRecordGapValue08858 : Nat := fullRecordGapCenterValue + 529982

theorem fullRecordGapTerm08858_eq_value :
    recordGapCenter + 529982 = fullRecordGapValue08858 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08858_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08858 (fullRecordGapValue08858 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08858_not_prime : ¬(recordGapCenter + 529982).Prime := by
  rw [fullRecordGapTerm08858_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08858, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08858_fast_pow_mod_ne_one

def fullRecordGapValue08859 : Nat := fullRecordGapCenterValue + 530148

theorem fullRecordGapTerm08859_eq_value :
    recordGapCenter + 530148 = fullRecordGapValue08859 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08859_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08859 (fullRecordGapValue08859 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08859_not_prime : ¬(recordGapCenter + 530148).Prime := by
  rw [fullRecordGapTerm08859_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08859, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08859_fast_pow_mod_ne_one

def fullRecordGapValue08860 : Nat := fullRecordGapCenterValue + 530268

theorem fullRecordGapTerm08860_eq_value :
    recordGapCenter + 530268 = fullRecordGapValue08860 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08860_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08860 (fullRecordGapValue08860 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08860_not_prime : ¬(recordGapCenter + 530268).Prime := by
  rw [fullRecordGapTerm08860_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08860, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08860_fast_pow_mod_ne_one

def fullRecordGapValue08861 : Nat := fullRecordGapCenterValue + 530408

theorem fullRecordGapTerm08861_eq_value :
    recordGapCenter + 530408 = fullRecordGapValue08861 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08861_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08861 (fullRecordGapValue08861 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08861_not_prime : ¬(recordGapCenter + 530408).Prime := by
  rw [fullRecordGapTerm08861_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08861, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08861_fast_pow_mod_ne_one

def fullRecordGapValue08862 : Nat := fullRecordGapCenterValue + 530436

theorem fullRecordGapTerm08862_eq_value :
    recordGapCenter + 530436 = fullRecordGapValue08862 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08862_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08862 (fullRecordGapValue08862 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08862_not_prime : ¬(recordGapCenter + 530436).Prime := by
  rw [fullRecordGapTerm08862_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08862, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08862_fast_pow_mod_ne_one

def fullRecordGapValue08863 : Nat := fullRecordGapCenterValue + 530492

theorem fullRecordGapTerm08863_eq_value :
    recordGapCenter + 530492 = fullRecordGapValue08863 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08863_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08863 (fullRecordGapValue08863 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08863_not_prime : ¬(recordGapCenter + 530492).Prime := by
  rw [fullRecordGapTerm08863_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08863, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08863_fast_pow_mod_ne_one

def fullRecordGapValue08864 : Nat := fullRecordGapCenterValue + 530546

theorem fullRecordGapTerm08864_eq_value :
    recordGapCenter + 530546 = fullRecordGapValue08864 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08864_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08864 (fullRecordGapValue08864 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08864_not_prime : ¬(recordGapCenter + 530546).Prime := by
  rw [fullRecordGapTerm08864_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08864, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08864_fast_pow_mod_ne_one

def fullRecordGapValue08865 : Nat := fullRecordGapCenterValue + 530562

theorem fullRecordGapTerm08865_eq_value :
    recordGapCenter + 530562 = fullRecordGapValue08865 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08865_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08865 (fullRecordGapValue08865 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08865_not_prime : ¬(recordGapCenter + 530562).Prime := by
  rw [fullRecordGapTerm08865_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08865, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08865_fast_pow_mod_ne_one

def fullRecordGapValue08866 : Nat := fullRecordGapCenterValue + 530588

theorem fullRecordGapTerm08866_eq_value :
    recordGapCenter + 530588 = fullRecordGapValue08866 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08866_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08866 (fullRecordGapValue08866 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08866_not_prime : ¬(recordGapCenter + 530588).Prime := by
  rw [fullRecordGapTerm08866_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08866, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08866_fast_pow_mod_ne_one

def fullRecordGapValue08867 : Nat := fullRecordGapCenterValue + 530652

theorem fullRecordGapTerm08867_eq_value :
    recordGapCenter + 530652 = fullRecordGapValue08867 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08867_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08867 (fullRecordGapValue08867 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08867_not_prime : ¬(recordGapCenter + 530652).Prime := by
  rw [fullRecordGapTerm08867_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08867, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08867_fast_pow_mod_ne_one

def fullRecordGapValue08868 : Nat := fullRecordGapCenterValue + 530666

theorem fullRecordGapTerm08868_eq_value :
    recordGapCenter + 530666 = fullRecordGapValue08868 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08868_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08868 (fullRecordGapValue08868 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08868_not_prime : ¬(recordGapCenter + 530666).Prime := by
  rw [fullRecordGapTerm08868_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08868, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08868_fast_pow_mod_ne_one

def fullRecordGapValue08869 : Nat := fullRecordGapCenterValue + 530762

theorem fullRecordGapTerm08869_eq_value :
    recordGapCenter + 530762 = fullRecordGapValue08869 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08869_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08869 (fullRecordGapValue08869 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08869_not_prime : ¬(recordGapCenter + 530762).Prime := by
  rw [fullRecordGapTerm08869_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08869, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08869_fast_pow_mod_ne_one

def fullRecordGapValue08870 : Nat := fullRecordGapCenterValue + 530846

theorem fullRecordGapTerm08870_eq_value :
    recordGapCenter + 530846 = fullRecordGapValue08870 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08870_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08870 (fullRecordGapValue08870 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08870_not_prime : ¬(recordGapCenter + 530846).Prime := by
  rw [fullRecordGapTerm08870_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08870, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08870_fast_pow_mod_ne_one

def fullRecordGapValue08871 : Nat := fullRecordGapCenterValue + 530888

theorem fullRecordGapTerm08871_eq_value :
    recordGapCenter + 530888 = fullRecordGapValue08871 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08871_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08871 (fullRecordGapValue08871 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08871_not_prime : ¬(recordGapCenter + 530888).Prime := by
  rw [fullRecordGapTerm08871_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08871, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08871_fast_pow_mod_ne_one

def fullRecordGapValue08872 : Nat := fullRecordGapCenterValue + 530918

theorem fullRecordGapTerm08872_eq_value :
    recordGapCenter + 530918 = fullRecordGapValue08872 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08872_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08872 (fullRecordGapValue08872 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08872_not_prime : ¬(recordGapCenter + 530918).Prime := by
  rw [fullRecordGapTerm08872_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08872, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08872_fast_pow_mod_ne_one

def fullRecordGapValue08873 : Nat := fullRecordGapCenterValue + 530930

theorem fullRecordGapTerm08873_eq_value :
    recordGapCenter + 530930 = fullRecordGapValue08873 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08873_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08873 (fullRecordGapValue08873 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08873_not_prime : ¬(recordGapCenter + 530930).Prime := by
  rw [fullRecordGapTerm08873_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08873, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08873_fast_pow_mod_ne_one

def fullRecordGapValue08874 : Nat := fullRecordGapCenterValue + 531078

theorem fullRecordGapTerm08874_eq_value :
    recordGapCenter + 531078 = fullRecordGapValue08874 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08874_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08874 (fullRecordGapValue08874 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08874_not_prime : ¬(recordGapCenter + 531078).Prime := by
  rw [fullRecordGapTerm08874_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08874, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08874_fast_pow_mod_ne_one

def fullRecordGapValue08875 : Nat := fullRecordGapCenterValue + 531122

theorem fullRecordGapTerm08875_eq_value :
    recordGapCenter + 531122 = fullRecordGapValue08875 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08875_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08875 (fullRecordGapValue08875 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08875_not_prime : ¬(recordGapCenter + 531122).Prime := by
  rw [fullRecordGapTerm08875_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08875, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08875_fast_pow_mod_ne_one

def fullRecordGapValue08876 : Nat := fullRecordGapCenterValue + 531170

theorem fullRecordGapTerm08876_eq_value :
    recordGapCenter + 531170 = fullRecordGapValue08876 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08876_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08876 (fullRecordGapValue08876 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08876_not_prime : ¬(recordGapCenter + 531170).Prime := by
  rw [fullRecordGapTerm08876_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08876, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08876_fast_pow_mod_ne_one

def fullRecordGapValue08877 : Nat := fullRecordGapCenterValue + 531242

theorem fullRecordGapTerm08877_eq_value :
    recordGapCenter + 531242 = fullRecordGapValue08877 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08877_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08877 (fullRecordGapValue08877 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08877_not_prime : ¬(recordGapCenter + 531242).Prime := by
  rw [fullRecordGapTerm08877_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08877, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08877_fast_pow_mod_ne_one

def fullRecordGapValue08878 : Nat := fullRecordGapCenterValue + 531458

theorem fullRecordGapTerm08878_eq_value :
    recordGapCenter + 531458 = fullRecordGapValue08878 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08878_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08878 (fullRecordGapValue08878 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08878_not_prime : ¬(recordGapCenter + 531458).Prime := by
  rw [fullRecordGapTerm08878_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08878, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08878_fast_pow_mod_ne_one

def fullRecordGapValue08879 : Nat := fullRecordGapCenterValue + 531470

theorem fullRecordGapTerm08879_eq_value :
    recordGapCenter + 531470 = fullRecordGapValue08879 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08879_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08879 (fullRecordGapValue08879 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08879_not_prime : ¬(recordGapCenter + 531470).Prime := by
  rw [fullRecordGapTerm08879_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08879, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08879_fast_pow_mod_ne_one

def fullRecordGapValue08880 : Nat := fullRecordGapCenterValue + 531546

theorem fullRecordGapTerm08880_eq_value :
    recordGapCenter + 531546 = fullRecordGapValue08880 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08880_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08880 (fullRecordGapValue08880 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08880_not_prime : ¬(recordGapCenter + 531546).Prime := by
  rw [fullRecordGapTerm08880_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08880, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08880_fast_pow_mod_ne_one

def fullRecordGapValue08881 : Nat := fullRecordGapCenterValue + 531548

theorem fullRecordGapTerm08881_eq_value :
    recordGapCenter + 531548 = fullRecordGapValue08881 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08881_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08881 (fullRecordGapValue08881 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08881_not_prime : ¬(recordGapCenter + 531548).Prime := by
  rw [fullRecordGapTerm08881_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08881, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08881_fast_pow_mod_ne_one

def fullRecordGapValue08882 : Nat := fullRecordGapCenterValue + 531638

theorem fullRecordGapTerm08882_eq_value :
    recordGapCenter + 531638 = fullRecordGapValue08882 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08882_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08882 (fullRecordGapValue08882 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08882_not_prime : ¬(recordGapCenter + 531638).Prime := by
  rw [fullRecordGapTerm08882_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08882, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08882_fast_pow_mod_ne_one

def fullRecordGapValue08883 : Nat := fullRecordGapCenterValue + 531722

theorem fullRecordGapTerm08883_eq_value :
    recordGapCenter + 531722 = fullRecordGapValue08883 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08883_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08883 (fullRecordGapValue08883 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08883_not_prime : ¬(recordGapCenter + 531722).Prime := by
  rw [fullRecordGapTerm08883_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08883, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08883_fast_pow_mod_ne_one

def fullRecordGapValue08884 : Nat := fullRecordGapCenterValue + 531746

theorem fullRecordGapTerm08884_eq_value :
    recordGapCenter + 531746 = fullRecordGapValue08884 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08884_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08884 (fullRecordGapValue08884 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08884_not_prime : ¬(recordGapCenter + 531746).Prime := by
  rw [fullRecordGapTerm08884_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08884, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08884_fast_pow_mod_ne_one

def fullRecordGapValue08885 : Nat := fullRecordGapCenterValue + 531906

theorem fullRecordGapTerm08885_eq_value :
    recordGapCenter + 531906 = fullRecordGapValue08885 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08885_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08885 (fullRecordGapValue08885 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08885_not_prime : ¬(recordGapCenter + 531906).Prime := by
  rw [fullRecordGapTerm08885_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08885, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08885_fast_pow_mod_ne_one

def fullRecordGapValue08886 : Nat := fullRecordGapCenterValue + 531966

theorem fullRecordGapTerm08886_eq_value :
    recordGapCenter + 531966 = fullRecordGapValue08886 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08886_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08886 (fullRecordGapValue08886 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08886_not_prime : ¬(recordGapCenter + 531966).Prime := by
  rw [fullRecordGapTerm08886_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08886, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08886_fast_pow_mod_ne_one

def fullRecordGapValue08887 : Nat := fullRecordGapCenterValue + 532002

theorem fullRecordGapTerm08887_eq_value :
    recordGapCenter + 532002 = fullRecordGapValue08887 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08887_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08887 (fullRecordGapValue08887 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08887_not_prime : ¬(recordGapCenter + 532002).Prime := by
  rw [fullRecordGapTerm08887_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08887, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08887_fast_pow_mod_ne_one

def fullRecordGapValue08888 : Nat := fullRecordGapCenterValue + 532010

theorem fullRecordGapTerm08888_eq_value :
    recordGapCenter + 532010 = fullRecordGapValue08888 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08888_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08888 (fullRecordGapValue08888 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08888_not_prime : ¬(recordGapCenter + 532010).Prime := by
  rw [fullRecordGapTerm08888_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08888, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08888_fast_pow_mod_ne_one

def fullRecordGapValue08889 : Nat := fullRecordGapCenterValue + 532106

theorem fullRecordGapTerm08889_eq_value :
    recordGapCenter + 532106 = fullRecordGapValue08889 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08889_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08889 (fullRecordGapValue08889 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08889_not_prime : ¬(recordGapCenter + 532106).Prime := by
  rw [fullRecordGapTerm08889_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08889, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08889_fast_pow_mod_ne_one

def fullRecordGapValue08890 : Nat := fullRecordGapCenterValue + 532212

theorem fullRecordGapTerm08890_eq_value :
    recordGapCenter + 532212 = fullRecordGapValue08890 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08890_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08890 (fullRecordGapValue08890 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08890_not_prime : ¬(recordGapCenter + 532212).Prime := by
  rw [fullRecordGapTerm08890_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08890, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08890_fast_pow_mod_ne_one

def fullRecordGapValue08891 : Nat := fullRecordGapCenterValue + 532310

theorem fullRecordGapTerm08891_eq_value :
    recordGapCenter + 532310 = fullRecordGapValue08891 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08891_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08891 (fullRecordGapValue08891 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08891_not_prime : ¬(recordGapCenter + 532310).Prime := by
  rw [fullRecordGapTerm08891_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08891, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08891_fast_pow_mod_ne_one

def fullRecordGapValue08892 : Nat := fullRecordGapCenterValue + 532326

theorem fullRecordGapTerm08892_eq_value :
    recordGapCenter + 532326 = fullRecordGapValue08892 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08892_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08892 (fullRecordGapValue08892 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08892_not_prime : ¬(recordGapCenter + 532326).Prime := by
  rw [fullRecordGapTerm08892_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08892, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08892_fast_pow_mod_ne_one

def fullRecordGapValue08893 : Nat := fullRecordGapCenterValue + 532388

theorem fullRecordGapTerm08893_eq_value :
    recordGapCenter + 532388 = fullRecordGapValue08893 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08893_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08893 (fullRecordGapValue08893 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08893_not_prime : ¬(recordGapCenter + 532388).Prime := by
  rw [fullRecordGapTerm08893_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08893, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08893_fast_pow_mod_ne_one

def fullRecordGapValue08894 : Nat := fullRecordGapCenterValue + 532400

theorem fullRecordGapTerm08894_eq_value :
    recordGapCenter + 532400 = fullRecordGapValue08894 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08894_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08894 (fullRecordGapValue08894 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08894_not_prime : ¬(recordGapCenter + 532400).Prime := by
  rw [fullRecordGapTerm08894_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08894, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08894_fast_pow_mod_ne_one

def fullRecordGapValue08895 : Nat := fullRecordGapCenterValue + 532436

theorem fullRecordGapTerm08895_eq_value :
    recordGapCenter + 532436 = fullRecordGapValue08895 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08895_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08895 (fullRecordGapValue08895 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08895_not_prime : ¬(recordGapCenter + 532436).Prime := by
  rw [fullRecordGapTerm08895_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08895, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08895_fast_pow_mod_ne_one

def fullRecordGapValue08896 : Nat := fullRecordGapCenterValue + 532442

theorem fullRecordGapTerm08896_eq_value :
    recordGapCenter + 532442 = fullRecordGapValue08896 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08896_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08896 (fullRecordGapValue08896 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08896_not_prime : ¬(recordGapCenter + 532442).Prime := by
  rw [fullRecordGapTerm08896_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08896, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08896_fast_pow_mod_ne_one

def fullRecordGapValue08897 : Nat := fullRecordGapCenterValue + 532446

theorem fullRecordGapTerm08897_eq_value :
    recordGapCenter + 532446 = fullRecordGapValue08897 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08897_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08897 (fullRecordGapValue08897 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08897_not_prime : ¬(recordGapCenter + 532446).Prime := by
  rw [fullRecordGapTerm08897_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08897, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08897_fast_pow_mod_ne_one

def fullRecordGapValue08898 : Nat := fullRecordGapCenterValue + 532802

theorem fullRecordGapTerm08898_eq_value :
    recordGapCenter + 532802 = fullRecordGapValue08898 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08898_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08898 (fullRecordGapValue08898 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08898_not_prime : ¬(recordGapCenter + 532802).Prime := by
  rw [fullRecordGapTerm08898_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08898, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08898_fast_pow_mod_ne_one

def fullRecordGapValue08899 : Nat := fullRecordGapCenterValue + 532806

theorem fullRecordGapTerm08899_eq_value :
    recordGapCenter + 532806 = fullRecordGapValue08899 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08899_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08899 (fullRecordGapValue08899 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08899_not_prime : ¬(recordGapCenter + 532806).Prime := by
  rw [fullRecordGapTerm08899_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08899, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08899_fast_pow_mod_ne_one

def fullRecordGapValue08900 : Nat := fullRecordGapCenterValue + 532808

theorem fullRecordGapTerm08900_eq_value :
    recordGapCenter + 532808 = fullRecordGapValue08900 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08900_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08900 (fullRecordGapValue08900 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08900_not_prime : ¬(recordGapCenter + 532808).Prime := by
  rw [fullRecordGapTerm08900_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08900, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08900_fast_pow_mod_ne_one

def fullRecordGapValue08901 : Nat := fullRecordGapCenterValue + 532842

theorem fullRecordGapTerm08901_eq_value :
    recordGapCenter + 532842 = fullRecordGapValue08901 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08901_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08901 (fullRecordGapValue08901 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08901_not_prime : ¬(recordGapCenter + 532842).Prime := by
  rw [fullRecordGapTerm08901_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08901, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08901_fast_pow_mod_ne_one

def fullRecordGapValue08902 : Nat := fullRecordGapCenterValue + 532866

theorem fullRecordGapTerm08902_eq_value :
    recordGapCenter + 532866 = fullRecordGapValue08902 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08902_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08902 (fullRecordGapValue08902 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08902_not_prime : ¬(recordGapCenter + 532866).Prime := by
  rw [fullRecordGapTerm08902_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08902, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08902_fast_pow_mod_ne_one

def fullRecordGapValue08903 : Nat := fullRecordGapCenterValue + 533108

theorem fullRecordGapTerm08903_eq_value :
    recordGapCenter + 533108 = fullRecordGapValue08903 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08903_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08903 (fullRecordGapValue08903 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08903_not_prime : ¬(recordGapCenter + 533108).Prime := by
  rw [fullRecordGapTerm08903_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08903, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08903_fast_pow_mod_ne_one

def fullRecordGapValue08904 : Nat := fullRecordGapCenterValue + 533118

theorem fullRecordGapTerm08904_eq_value :
    recordGapCenter + 533118 = fullRecordGapValue08904 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08904_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08904 (fullRecordGapValue08904 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08904_not_prime : ¬(recordGapCenter + 533118).Prime := by
  rw [fullRecordGapTerm08904_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08904, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08904_fast_pow_mod_ne_one

def fullRecordGapValue08905 : Nat := fullRecordGapCenterValue + 533270

theorem fullRecordGapTerm08905_eq_value :
    recordGapCenter + 533270 = fullRecordGapValue08905 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08905_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08905 (fullRecordGapValue08905 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08905_not_prime : ¬(recordGapCenter + 533270).Prime := by
  rw [fullRecordGapTerm08905_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08905, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08905_fast_pow_mod_ne_one

def fullRecordGapValue08906 : Nat := fullRecordGapCenterValue + 533348

theorem fullRecordGapTerm08906_eq_value :
    recordGapCenter + 533348 = fullRecordGapValue08906 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08906_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08906 (fullRecordGapValue08906 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08906_not_prime : ¬(recordGapCenter + 533348).Prime := by
  rw [fullRecordGapTerm08906_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08906, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08906_fast_pow_mod_ne_one

def fullRecordGapValue08907 : Nat := fullRecordGapCenterValue + 533366

theorem fullRecordGapTerm08907_eq_value :
    recordGapCenter + 533366 = fullRecordGapValue08907 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08907_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08907 (fullRecordGapValue08907 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08907_not_prime : ¬(recordGapCenter + 533366).Prime := by
  rw [fullRecordGapTerm08907_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08907, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08907_fast_pow_mod_ne_one

def fullRecordGapValue08908 : Nat := fullRecordGapCenterValue + 533396

theorem fullRecordGapTerm08908_eq_value :
    recordGapCenter + 533396 = fullRecordGapValue08908 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08908_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08908 (fullRecordGapValue08908 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08908_not_prime : ¬(recordGapCenter + 533396).Prime := by
  rw [fullRecordGapTerm08908_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08908, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08908_fast_pow_mod_ne_one

def fullRecordGapValue08909 : Nat := fullRecordGapCenterValue + 533436

theorem fullRecordGapTerm08909_eq_value :
    recordGapCenter + 533436 = fullRecordGapValue08909 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08909_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08909 (fullRecordGapValue08909 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08909_not_prime : ¬(recordGapCenter + 533436).Prime := by
  rw [fullRecordGapTerm08909_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08909, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08909_fast_pow_mod_ne_one

def fullRecordGapValue08910 : Nat := fullRecordGapCenterValue + 533438

theorem fullRecordGapTerm08910_eq_value :
    recordGapCenter + 533438 = fullRecordGapValue08910 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08910_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08910 (fullRecordGapValue08910 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08910_not_prime : ¬(recordGapCenter + 533438).Prime := by
  rw [fullRecordGapTerm08910_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08910, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08910_fast_pow_mod_ne_one

def fullRecordGapValue08911 : Nat := fullRecordGapCenterValue + 533576

theorem fullRecordGapTerm08911_eq_value :
    recordGapCenter + 533576 = fullRecordGapValue08911 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08911_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08911 (fullRecordGapValue08911 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08911_not_prime : ¬(recordGapCenter + 533576).Prime := by
  rw [fullRecordGapTerm08911_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08911, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08911_fast_pow_mod_ne_one

def fullRecordGapValue08912 : Nat := fullRecordGapCenterValue + 533612

theorem fullRecordGapTerm08912_eq_value :
    recordGapCenter + 533612 = fullRecordGapValue08912 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08912_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08912 (fullRecordGapValue08912 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08912_not_prime : ¬(recordGapCenter + 533612).Prime := by
  rw [fullRecordGapTerm08912_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08912, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08912_fast_pow_mod_ne_one

def fullRecordGapValue08913 : Nat := fullRecordGapCenterValue + 533642

theorem fullRecordGapTerm08913_eq_value :
    recordGapCenter + 533642 = fullRecordGapValue08913 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08913_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08913 (fullRecordGapValue08913 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08913_not_prime : ¬(recordGapCenter + 533642).Prime := by
  rw [fullRecordGapTerm08913_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08913, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08913_fast_pow_mod_ne_one

def fullRecordGapValue08914 : Nat := fullRecordGapCenterValue + 533678

theorem fullRecordGapTerm08914_eq_value :
    recordGapCenter + 533678 = fullRecordGapValue08914 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08914_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08914 (fullRecordGapValue08914 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08914_not_prime : ¬(recordGapCenter + 533678).Prime := by
  rw [fullRecordGapTerm08914_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08914, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08914_fast_pow_mod_ne_one

def fullRecordGapValue08915 : Nat := fullRecordGapCenterValue + 533726

theorem fullRecordGapTerm08915_eq_value :
    recordGapCenter + 533726 = fullRecordGapValue08915 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08915_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08915 (fullRecordGapValue08915 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08915_not_prime : ¬(recordGapCenter + 533726).Prime := by
  rw [fullRecordGapTerm08915_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08915, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08915_fast_pow_mod_ne_one

def fullRecordGapValue08916 : Nat := fullRecordGapCenterValue + 533810

theorem fullRecordGapTerm08916_eq_value :
    recordGapCenter + 533810 = fullRecordGapValue08916 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08916_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08916 (fullRecordGapValue08916 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08916_not_prime : ¬(recordGapCenter + 533810).Prime := by
  rw [fullRecordGapTerm08916_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08916, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08916_fast_pow_mod_ne_one

def fullRecordGapValue08917 : Nat := fullRecordGapCenterValue + 533906

theorem fullRecordGapTerm08917_eq_value :
    recordGapCenter + 533906 = fullRecordGapValue08917 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08917_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08917 (fullRecordGapValue08917 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08917_not_prime : ¬(recordGapCenter + 533906).Prime := by
  rw [fullRecordGapTerm08917_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08917, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08917_fast_pow_mod_ne_one

def fullRecordGapValue08918 : Nat := fullRecordGapCenterValue + 533942

theorem fullRecordGapTerm08918_eq_value :
    recordGapCenter + 533942 = fullRecordGapValue08918 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08918_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08918 (fullRecordGapValue08918 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08918_not_prime : ¬(recordGapCenter + 533942).Prime := by
  rw [fullRecordGapTerm08918_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08918, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08918_fast_pow_mod_ne_one

def fullRecordGapValue08919 : Nat := fullRecordGapCenterValue + 533972

theorem fullRecordGapTerm08919_eq_value :
    recordGapCenter + 533972 = fullRecordGapValue08919 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08919_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08919 (fullRecordGapValue08919 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08919_not_prime : ¬(recordGapCenter + 533972).Prime := by
  rw [fullRecordGapTerm08919_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08919, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08919_fast_pow_mod_ne_one

def fullRecordGapValue08920 : Nat := fullRecordGapCenterValue + 533982

theorem fullRecordGapTerm08920_eq_value :
    recordGapCenter + 533982 = fullRecordGapValue08920 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08920_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08920 (fullRecordGapValue08920 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08920_not_prime : ¬(recordGapCenter + 533982).Prime := by
  rw [fullRecordGapTerm08920_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08920, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08920_fast_pow_mod_ne_one

def fullRecordGapValue08921 : Nat := fullRecordGapCenterValue + 533996

theorem fullRecordGapTerm08921_eq_value :
    recordGapCenter + 533996 = fullRecordGapValue08921 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08921_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08921 (fullRecordGapValue08921 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08921_not_prime : ¬(recordGapCenter + 533996).Prime := by
  rw [fullRecordGapTerm08921_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08921, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08921_fast_pow_mod_ne_one

def fullRecordGapValue08922 : Nat := fullRecordGapCenterValue + 534098

theorem fullRecordGapTerm08922_eq_value :
    recordGapCenter + 534098 = fullRecordGapValue08922 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08922_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08922 (fullRecordGapValue08922 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08922_not_prime : ¬(recordGapCenter + 534098).Prime := by
  rw [fullRecordGapTerm08922_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08922, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08922_fast_pow_mod_ne_one

def fullRecordGapValue08923 : Nat := fullRecordGapCenterValue + 534102

theorem fullRecordGapTerm08923_eq_value :
    recordGapCenter + 534102 = fullRecordGapValue08923 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08923_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08923 (fullRecordGapValue08923 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08923_not_prime : ¬(recordGapCenter + 534102).Prime := by
  rw [fullRecordGapTerm08923_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08923, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08923_fast_pow_mod_ne_one

def fullRecordGapValue08924 : Nat := fullRecordGapCenterValue + 534426

theorem fullRecordGapTerm08924_eq_value :
    recordGapCenter + 534426 = fullRecordGapValue08924 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08924_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08924 (fullRecordGapValue08924 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08924_not_prime : ¬(recordGapCenter + 534426).Prime := by
  rw [fullRecordGapTerm08924_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08924, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08924_fast_pow_mod_ne_one

def fullRecordGapValue08925 : Nat := fullRecordGapCenterValue + 534516

theorem fullRecordGapTerm08925_eq_value :
    recordGapCenter + 534516 = fullRecordGapValue08925 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08925_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08925 (fullRecordGapValue08925 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08925_not_prime : ¬(recordGapCenter + 534516).Prime := by
  rw [fullRecordGapTerm08925_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08925, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08925_fast_pow_mod_ne_one

def fullRecordGapValue08926 : Nat := fullRecordGapCenterValue + 534518

theorem fullRecordGapTerm08926_eq_value :
    recordGapCenter + 534518 = fullRecordGapValue08926 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08926_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08926 (fullRecordGapValue08926 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08926_not_prime : ¬(recordGapCenter + 534518).Prime := by
  rw [fullRecordGapTerm08926_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08926, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08926_fast_pow_mod_ne_one

def fullRecordGapValue08927 : Nat := fullRecordGapCenterValue + 534542

theorem fullRecordGapTerm08927_eq_value :
    recordGapCenter + 534542 = fullRecordGapValue08927 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08927_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08927 (fullRecordGapValue08927 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08927_not_prime : ¬(recordGapCenter + 534542).Prime := by
  rw [fullRecordGapTerm08927_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08927, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08927_fast_pow_mod_ne_one

def fullRecordGapValue08928 : Nat := fullRecordGapCenterValue + 534600

theorem fullRecordGapTerm08928_eq_value :
    recordGapCenter + 534600 = fullRecordGapValue08928 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08928_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08928 (fullRecordGapValue08928 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08928_not_prime : ¬(recordGapCenter + 534600).Prime := by
  rw [fullRecordGapTerm08928_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08928, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08928_fast_pow_mod_ne_one

def fullRecordGapValue08929 : Nat := fullRecordGapCenterValue + 534642

theorem fullRecordGapTerm08929_eq_value :
    recordGapCenter + 534642 = fullRecordGapValue08929 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08929_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08929 (fullRecordGapValue08929 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08929_not_prime : ¬(recordGapCenter + 534642).Prime := by
  rw [fullRecordGapTerm08929_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08929, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08929_fast_pow_mod_ne_one

def fullRecordGapValue08930 : Nat := fullRecordGapCenterValue + 534782

theorem fullRecordGapTerm08930_eq_value :
    recordGapCenter + 534782 = fullRecordGapValue08930 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08930_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08930 (fullRecordGapValue08930 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08930_not_prime : ¬(recordGapCenter + 534782).Prime := by
  rw [fullRecordGapTerm08930_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08930, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08930_fast_pow_mod_ne_one

def fullRecordGapValue08931 : Nat := fullRecordGapCenterValue + 534822

theorem fullRecordGapTerm08931_eq_value :
    recordGapCenter + 534822 = fullRecordGapValue08931 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08931_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08931 (fullRecordGapValue08931 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08931_not_prime : ¬(recordGapCenter + 534822).Prime := by
  rw [fullRecordGapTerm08931_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08931, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08931_fast_pow_mod_ne_one

def fullRecordGapValue08932 : Nat := fullRecordGapCenterValue + 534902

theorem fullRecordGapTerm08932_eq_value :
    recordGapCenter + 534902 = fullRecordGapValue08932 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08932_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08932 (fullRecordGapValue08932 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08932_not_prime : ¬(recordGapCenter + 534902).Prime := by
  rw [fullRecordGapTerm08932_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08932, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08932_fast_pow_mod_ne_one

def fullRecordGapValue08933 : Nat := fullRecordGapCenterValue + 534938

theorem fullRecordGapTerm08933_eq_value :
    recordGapCenter + 534938 = fullRecordGapValue08933 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08933_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08933 (fullRecordGapValue08933 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08933_not_prime : ¬(recordGapCenter + 534938).Prime := by
  rw [fullRecordGapTerm08933_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08933, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08933_fast_pow_mod_ne_one

def fullRecordGapValue08934 : Nat := fullRecordGapCenterValue + 534962

theorem fullRecordGapTerm08934_eq_value :
    recordGapCenter + 534962 = fullRecordGapValue08934 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08934_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08934 (fullRecordGapValue08934 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08934_not_prime : ¬(recordGapCenter + 534962).Prime := by
  rw [fullRecordGapTerm08934_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08934, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08934_fast_pow_mod_ne_one

def fullRecordGapValue08935 : Nat := fullRecordGapCenterValue + 535070

theorem fullRecordGapTerm08935_eq_value :
    recordGapCenter + 535070 = fullRecordGapValue08935 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08935_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08935 (fullRecordGapValue08935 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08935_not_prime : ¬(recordGapCenter + 535070).Prime := by
  rw [fullRecordGapTerm08935_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08935, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08935_fast_pow_mod_ne_one

def fullRecordGapValue08936 : Nat := fullRecordGapCenterValue + 535076

theorem fullRecordGapTerm08936_eq_value :
    recordGapCenter + 535076 = fullRecordGapValue08936 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08936_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08936 (fullRecordGapValue08936 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08936_not_prime : ¬(recordGapCenter + 535076).Prime := by
  rw [fullRecordGapTerm08936_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08936, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08936_fast_pow_mod_ne_one

def fullRecordGapValue08937 : Nat := fullRecordGapCenterValue + 535202

theorem fullRecordGapTerm08937_eq_value :
    recordGapCenter + 535202 = fullRecordGapValue08937 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08937_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08937 (fullRecordGapValue08937 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08937_not_prime : ¬(recordGapCenter + 535202).Prime := by
  rw [fullRecordGapTerm08937_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08937, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08937_fast_pow_mod_ne_one

def fullRecordGapValue08938 : Nat := fullRecordGapCenterValue + 535286

theorem fullRecordGapTerm08938_eq_value :
    recordGapCenter + 535286 = fullRecordGapValue08938 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08938_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08938 (fullRecordGapValue08938 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08938_not_prime : ¬(recordGapCenter + 535286).Prime := by
  rw [fullRecordGapTerm08938_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08938, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08938_fast_pow_mod_ne_one

def fullRecordGapValue08939 : Nat := fullRecordGapCenterValue + 535362

theorem fullRecordGapTerm08939_eq_value :
    recordGapCenter + 535362 = fullRecordGapValue08939 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08939_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08939 (fullRecordGapValue08939 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08939_not_prime : ¬(recordGapCenter + 535362).Prime := by
  rw [fullRecordGapTerm08939_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08939, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08939_fast_pow_mod_ne_one

def fullRecordGapValue08940 : Nat := fullRecordGapCenterValue + 535386

theorem fullRecordGapTerm08940_eq_value :
    recordGapCenter + 535386 = fullRecordGapValue08940 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08940_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08940 (fullRecordGapValue08940 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08940_not_prime : ¬(recordGapCenter + 535386).Prime := by
  rw [fullRecordGapTerm08940_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08940, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08940_fast_pow_mod_ne_one

def fullRecordGapValue08941 : Nat := fullRecordGapCenterValue + 535442

theorem fullRecordGapTerm08941_eq_value :
    recordGapCenter + 535442 = fullRecordGapValue08941 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08941_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08941 (fullRecordGapValue08941 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08941_not_prime : ¬(recordGapCenter + 535442).Prime := by
  rw [fullRecordGapTerm08941_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08941, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08941_fast_pow_mod_ne_one

def fullRecordGapValue08942 : Nat := fullRecordGapCenterValue + 535452

theorem fullRecordGapTerm08942_eq_value :
    recordGapCenter + 535452 = fullRecordGapValue08942 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08942_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08942 (fullRecordGapValue08942 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08942_not_prime : ¬(recordGapCenter + 535452).Prime := by
  rw [fullRecordGapTerm08942_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08942, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08942_fast_pow_mod_ne_one

def fullRecordGapValue08943 : Nat := fullRecordGapCenterValue + 535566

theorem fullRecordGapTerm08943_eq_value :
    recordGapCenter + 535566 = fullRecordGapValue08943 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08943_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08943 (fullRecordGapValue08943 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08943_not_prime : ¬(recordGapCenter + 535566).Prime := by
  rw [fullRecordGapTerm08943_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08943, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08943_fast_pow_mod_ne_one

def fullRecordGapValue08944 : Nat := fullRecordGapCenterValue + 535592

theorem fullRecordGapTerm08944_eq_value :
    recordGapCenter + 535592 = fullRecordGapValue08944 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08944_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08944 (fullRecordGapValue08944 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08944_not_prime : ¬(recordGapCenter + 535592).Prime := by
  rw [fullRecordGapTerm08944_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08944, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08944_fast_pow_mod_ne_one

def fullRecordGapValue08945 : Nat := fullRecordGapCenterValue + 535802

theorem fullRecordGapTerm08945_eq_value :
    recordGapCenter + 535802 = fullRecordGapValue08945 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08945_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08945 (fullRecordGapValue08945 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08945_not_prime : ¬(recordGapCenter + 535802).Prime := by
  rw [fullRecordGapTerm08945_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08945, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08945_fast_pow_mod_ne_one

def fullRecordGapValue08946 : Nat := fullRecordGapCenterValue + 535812

theorem fullRecordGapTerm08946_eq_value :
    recordGapCenter + 535812 = fullRecordGapValue08946 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08946_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08946 (fullRecordGapValue08946 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08946_not_prime : ¬(recordGapCenter + 535812).Prime := by
  rw [fullRecordGapTerm08946_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08946, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08946_fast_pow_mod_ne_one

def fullRecordGapValue08947 : Nat := fullRecordGapCenterValue + 535818

theorem fullRecordGapTerm08947_eq_value :
    recordGapCenter + 535818 = fullRecordGapValue08947 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08947_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08947 (fullRecordGapValue08947 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08947_not_prime : ¬(recordGapCenter + 535818).Prime := by
  rw [fullRecordGapTerm08947_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08947, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08947_fast_pow_mod_ne_one

def fullRecordGapValue08948 : Nat := fullRecordGapCenterValue + 535826

theorem fullRecordGapTerm08948_eq_value :
    recordGapCenter + 535826 = fullRecordGapValue08948 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08948_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08948 (fullRecordGapValue08948 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08948_not_prime : ¬(recordGapCenter + 535826).Prime := by
  rw [fullRecordGapTerm08948_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08948, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08948_fast_pow_mod_ne_one

def fullRecordGapValue08949 : Nat := fullRecordGapCenterValue + 535910

theorem fullRecordGapTerm08949_eq_value :
    recordGapCenter + 535910 = fullRecordGapValue08949 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08949_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08949 (fullRecordGapValue08949 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08949_not_prime : ¬(recordGapCenter + 535910).Prime := by
  rw [fullRecordGapTerm08949_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08949, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08949_fast_pow_mod_ne_one

def fullRecordGapValue08950 : Nat := fullRecordGapCenterValue + 536006

theorem fullRecordGapTerm08950_eq_value :
    recordGapCenter + 536006 = fullRecordGapValue08950 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08950_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08950 (fullRecordGapValue08950 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08950_not_prime : ¬(recordGapCenter + 536006).Prime := by
  rw [fullRecordGapTerm08950_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08950, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08950_fast_pow_mod_ne_one

def fullRecordGapValue08951 : Nat := fullRecordGapCenterValue + 536126

theorem fullRecordGapTerm08951_eq_value :
    recordGapCenter + 536126 = fullRecordGapValue08951 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08951_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08951 (fullRecordGapValue08951 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08951_not_prime : ¬(recordGapCenter + 536126).Prime := by
  rw [fullRecordGapTerm08951_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08951, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08951_fast_pow_mod_ne_one

def fullRecordGapValue08952 : Nat := fullRecordGapCenterValue + 536138

theorem fullRecordGapTerm08952_eq_value :
    recordGapCenter + 536138 = fullRecordGapValue08952 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08952_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08952 (fullRecordGapValue08952 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08952_not_prime : ¬(recordGapCenter + 536138).Prime := by
  rw [fullRecordGapTerm08952_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08952, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08952_fast_pow_mod_ne_one

def fullRecordGapValue08953 : Nat := fullRecordGapCenterValue + 536168

theorem fullRecordGapTerm08953_eq_value :
    recordGapCenter + 536168 = fullRecordGapValue08953 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08953_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08953 (fullRecordGapValue08953 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08953_not_prime : ¬(recordGapCenter + 536168).Prime := by
  rw [fullRecordGapTerm08953_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08953, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08953_fast_pow_mod_ne_one

def fullRecordGapValue08954 : Nat := fullRecordGapCenterValue + 536196

theorem fullRecordGapTerm08954_eq_value :
    recordGapCenter + 536196 = fullRecordGapValue08954 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08954_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08954 (fullRecordGapValue08954 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08954_not_prime : ¬(recordGapCenter + 536196).Prime := by
  rw [fullRecordGapTerm08954_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08954, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08954_fast_pow_mod_ne_one

def fullRecordGapValue08955 : Nat := fullRecordGapCenterValue + 536226

theorem fullRecordGapTerm08955_eq_value :
    recordGapCenter + 536226 = fullRecordGapValue08955 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08955_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08955 (fullRecordGapValue08955 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08955_not_prime : ¬(recordGapCenter + 536226).Prime := by
  rw [fullRecordGapTerm08955_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08955, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08955_fast_pow_mod_ne_one

def fullRecordGapValue08956 : Nat := fullRecordGapCenterValue + 536286

theorem fullRecordGapTerm08956_eq_value :
    recordGapCenter + 536286 = fullRecordGapValue08956 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08956_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08956 (fullRecordGapValue08956 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08956_not_prime : ¬(recordGapCenter + 536286).Prime := by
  rw [fullRecordGapTerm08956_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08956, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08956_fast_pow_mod_ne_one

def fullRecordGapValue08957 : Nat := fullRecordGapCenterValue + 536306

theorem fullRecordGapTerm08957_eq_value :
    recordGapCenter + 536306 = fullRecordGapValue08957 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08957_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08957 (fullRecordGapValue08957 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08957_not_prime : ¬(recordGapCenter + 536306).Prime := by
  rw [fullRecordGapTerm08957_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08957, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08957_fast_pow_mod_ne_one

def fullRecordGapValue08958 : Nat := fullRecordGapCenterValue + 536342

theorem fullRecordGapTerm08958_eq_value :
    recordGapCenter + 536342 = fullRecordGapValue08958 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08958_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08958 (fullRecordGapValue08958 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08958_not_prime : ¬(recordGapCenter + 536342).Prime := by
  rw [fullRecordGapTerm08958_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08958, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08958_fast_pow_mod_ne_one

def fullRecordGapValue08959 : Nat := fullRecordGapCenterValue + 536348

theorem fullRecordGapTerm08959_eq_value :
    recordGapCenter + 536348 = fullRecordGapValue08959 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08959_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08959 (fullRecordGapValue08959 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08959_not_prime : ¬(recordGapCenter + 536348).Prime := by
  rw [fullRecordGapTerm08959_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08959, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08959_fast_pow_mod_ne_one

def fullRecordGapValue08960 : Nat := fullRecordGapCenterValue + 536372

theorem fullRecordGapTerm08960_eq_value :
    recordGapCenter + 536372 = fullRecordGapValue08960 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral08960_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue08960 (fullRecordGapValue08960 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm08960_not_prime : ¬(recordGapCenter + 536372).Prime := by
  rw [fullRecordGapTerm08960_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue08960, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral08960_fast_pow_mod_ne_one

end PrimeFactorUnimodality
