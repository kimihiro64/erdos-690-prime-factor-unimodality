import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue02561 : Nat := fullRecordGapCenterValue - 236122

theorem fullRecordGapTerm02561_eq_value :
    recordGapCenter - 236122 = fullRecordGapValue02561 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02561_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02561 (fullRecordGapValue02561 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02561_not_prime : ¬(recordGapCenter - 236122).Prime := by
  rw [fullRecordGapTerm02561_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02561, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02561_fast_pow_mod_ne_one

def fullRecordGapValue02562 : Nat := fullRecordGapCenterValue - 236092

theorem fullRecordGapTerm02562_eq_value :
    recordGapCenter - 236092 = fullRecordGapValue02562 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02562_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02562 (fullRecordGapValue02562 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02562_not_prime : ¬(recordGapCenter - 236092).Prime := by
  rw [fullRecordGapTerm02562_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02562, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02562_fast_pow_mod_ne_one

def fullRecordGapValue02563 : Nat := fullRecordGapCenterValue - 236044

theorem fullRecordGapTerm02563_eq_value :
    recordGapCenter - 236044 = fullRecordGapValue02563 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02563_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02563 (fullRecordGapValue02563 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02563_not_prime : ¬(recordGapCenter - 236044).Prime := by
  rw [fullRecordGapTerm02563_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02563, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02563_fast_pow_mod_ne_one

def fullRecordGapValue02564 : Nat := fullRecordGapCenterValue - 235918

theorem fullRecordGapTerm02564_eq_value :
    recordGapCenter - 235918 = fullRecordGapValue02564 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02564_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02564 (fullRecordGapValue02564 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02564_not_prime : ¬(recordGapCenter - 235918).Prime := by
  rw [fullRecordGapTerm02564_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02564, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02564_fast_pow_mod_ne_one

def fullRecordGapValue02565 : Nat := fullRecordGapCenterValue - 235678

theorem fullRecordGapTerm02565_eq_value :
    recordGapCenter - 235678 = fullRecordGapValue02565 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02565_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02565 (fullRecordGapValue02565 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02565_not_prime : ¬(recordGapCenter - 235678).Prime := by
  rw [fullRecordGapTerm02565_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02565, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02565_fast_pow_mod_ne_one

def fullRecordGapValue02566 : Nat := fullRecordGapCenterValue - 235618

theorem fullRecordGapTerm02566_eq_value :
    recordGapCenter - 235618 = fullRecordGapValue02566 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02566_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02566 (fullRecordGapValue02566 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02566_not_prime : ¬(recordGapCenter - 235618).Prime := by
  rw [fullRecordGapTerm02566_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02566, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02566_fast_pow_mod_ne_one

def fullRecordGapValue02567 : Nat := fullRecordGapCenterValue - 235594

theorem fullRecordGapTerm02567_eq_value :
    recordGapCenter - 235594 = fullRecordGapValue02567 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02567_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02567 (fullRecordGapValue02567 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02567_not_prime : ¬(recordGapCenter - 235594).Prime := by
  rw [fullRecordGapTerm02567_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02567, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02567_fast_pow_mod_ne_one

def fullRecordGapValue02568 : Nat := fullRecordGapCenterValue - 235402

theorem fullRecordGapTerm02568_eq_value :
    recordGapCenter - 235402 = fullRecordGapValue02568 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02568_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02568 (fullRecordGapValue02568 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02568_not_prime : ¬(recordGapCenter - 235402).Prime := by
  rw [fullRecordGapTerm02568_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02568, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02568_fast_pow_mod_ne_one

def fullRecordGapValue02569 : Nat := fullRecordGapCenterValue - 235200

theorem fullRecordGapTerm02569_eq_value :
    recordGapCenter - 235200 = fullRecordGapValue02569 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02569_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02569 (fullRecordGapValue02569 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02569_not_prime : ¬(recordGapCenter - 235200).Prime := by
  rw [fullRecordGapTerm02569_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02569, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02569_fast_pow_mod_ne_one

def fullRecordGapValue02570 : Nat := fullRecordGapCenterValue - 234862

theorem fullRecordGapTerm02570_eq_value :
    recordGapCenter - 234862 = fullRecordGapValue02570 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02570_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02570 (fullRecordGapValue02570 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02570_not_prime : ¬(recordGapCenter - 234862).Prime := by
  rw [fullRecordGapTerm02570_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02570, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02570_fast_pow_mod_ne_one

def fullRecordGapValue02571 : Nat := fullRecordGapCenterValue - 234772

theorem fullRecordGapTerm02571_eq_value :
    recordGapCenter - 234772 = fullRecordGapValue02571 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02571_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02571 (fullRecordGapValue02571 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02571_not_prime : ¬(recordGapCenter - 234772).Prime := by
  rw [fullRecordGapTerm02571_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02571, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02571_fast_pow_mod_ne_one

def fullRecordGapValue02572 : Nat := fullRecordGapCenterValue - 234748

theorem fullRecordGapTerm02572_eq_value :
    recordGapCenter - 234748 = fullRecordGapValue02572 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02572_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02572 (fullRecordGapValue02572 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02572_not_prime : ¬(recordGapCenter - 234748).Prime := by
  rw [fullRecordGapTerm02572_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02572, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02572_fast_pow_mod_ne_one

def fullRecordGapValue02573 : Nat := fullRecordGapCenterValue - 234742

theorem fullRecordGapTerm02573_eq_value :
    recordGapCenter - 234742 = fullRecordGapValue02573 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02573_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02573 (fullRecordGapValue02573 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02573_not_prime : ¬(recordGapCenter - 234742).Prime := by
  rw [fullRecordGapTerm02573_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02573, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02573_fast_pow_mod_ne_one

def fullRecordGapValue02574 : Nat := fullRecordGapCenterValue - 234538

theorem fullRecordGapTerm02574_eq_value :
    recordGapCenter - 234538 = fullRecordGapValue02574 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02574_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02574 (fullRecordGapValue02574 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02574_not_prime : ¬(recordGapCenter - 234538).Prime := by
  rw [fullRecordGapTerm02574_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02574, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02574_fast_pow_mod_ne_one

def fullRecordGapValue02575 : Nat := fullRecordGapCenterValue - 234478

theorem fullRecordGapTerm02575_eq_value :
    recordGapCenter - 234478 = fullRecordGapValue02575 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02575_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02575 (fullRecordGapValue02575 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02575_not_prime : ¬(recordGapCenter - 234478).Prime := by
  rw [fullRecordGapTerm02575_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02575, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02575_fast_pow_mod_ne_one

def fullRecordGapValue02576 : Nat := fullRecordGapCenterValue - 234418

theorem fullRecordGapTerm02576_eq_value :
    recordGapCenter - 234418 = fullRecordGapValue02576 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02576_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02576 (fullRecordGapValue02576 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02576_not_prime : ¬(recordGapCenter - 234418).Prime := by
  rw [fullRecordGapTerm02576_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02576, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02576_fast_pow_mod_ne_one

def fullRecordGapValue02577 : Nat := fullRecordGapCenterValue - 234202

theorem fullRecordGapTerm02577_eq_value :
    recordGapCenter - 234202 = fullRecordGapValue02577 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02577_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02577 (fullRecordGapValue02577 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02577_not_prime : ¬(recordGapCenter - 234202).Prime := by
  rw [fullRecordGapTerm02577_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02577, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02577_fast_pow_mod_ne_one

def fullRecordGapValue02578 : Nat := fullRecordGapCenterValue - 234148

theorem fullRecordGapTerm02578_eq_value :
    recordGapCenter - 234148 = fullRecordGapValue02578 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02578_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02578 (fullRecordGapValue02578 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02578_not_prime : ¬(recordGapCenter - 234148).Prime := by
  rw [fullRecordGapTerm02578_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02578, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02578_fast_pow_mod_ne_one

def fullRecordGapValue02579 : Nat := fullRecordGapCenterValue - 233698

theorem fullRecordGapTerm02579_eq_value :
    recordGapCenter - 233698 = fullRecordGapValue02579 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02579_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02579 (fullRecordGapValue02579 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02579_not_prime : ¬(recordGapCenter - 233698).Prime := by
  rw [fullRecordGapTerm02579_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02579, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02579_fast_pow_mod_ne_one

def fullRecordGapValue02580 : Nat := fullRecordGapCenterValue - 233638

theorem fullRecordGapTerm02580_eq_value :
    recordGapCenter - 233638 = fullRecordGapValue02580 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02580_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02580 (fullRecordGapValue02580 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02580_not_prime : ¬(recordGapCenter - 233638).Prime := by
  rw [fullRecordGapTerm02580_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02580, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02580_fast_pow_mod_ne_one

def fullRecordGapValue02581 : Nat := fullRecordGapCenterValue - 233572

theorem fullRecordGapTerm02581_eq_value :
    recordGapCenter - 233572 = fullRecordGapValue02581 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02581_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02581 (fullRecordGapValue02581 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02581_not_prime : ¬(recordGapCenter - 233572).Prime := by
  rw [fullRecordGapTerm02581_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02581, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02581_fast_pow_mod_ne_one

def fullRecordGapValue02582 : Nat := fullRecordGapCenterValue - 233452

theorem fullRecordGapTerm02582_eq_value :
    recordGapCenter - 233452 = fullRecordGapValue02582 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02582_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02582 (fullRecordGapValue02582 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02582_not_prime : ¬(recordGapCenter - 233452).Prime := by
  rw [fullRecordGapTerm02582_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02582, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02582_fast_pow_mod_ne_one

def fullRecordGapValue02583 : Nat := fullRecordGapCenterValue - 233284

theorem fullRecordGapTerm02583_eq_value :
    recordGapCenter - 233284 = fullRecordGapValue02583 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02583_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02583 (fullRecordGapValue02583 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02583_not_prime : ¬(recordGapCenter - 233284).Prime := by
  rw [fullRecordGapTerm02583_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02583, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02583_fast_pow_mod_ne_one

def fullRecordGapValue02584 : Nat := fullRecordGapCenterValue - 233074

theorem fullRecordGapTerm02584_eq_value :
    recordGapCenter - 233074 = fullRecordGapValue02584 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02584_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02584 (fullRecordGapValue02584 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02584_not_prime : ¬(recordGapCenter - 233074).Prime := by
  rw [fullRecordGapTerm02584_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02584, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02584_fast_pow_mod_ne_one

def fullRecordGapValue02585 : Nat := fullRecordGapCenterValue - 233062

theorem fullRecordGapTerm02585_eq_value :
    recordGapCenter - 233062 = fullRecordGapValue02585 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02585_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02585 (fullRecordGapValue02585 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02585_not_prime : ¬(recordGapCenter - 233062).Prime := by
  rw [fullRecordGapTerm02585_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02585, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02585_fast_pow_mod_ne_one

def fullRecordGapValue02586 : Nat := fullRecordGapCenterValue - 232822

theorem fullRecordGapTerm02586_eq_value :
    recordGapCenter - 232822 = fullRecordGapValue02586 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02586_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02586 (fullRecordGapValue02586 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02586_not_prime : ¬(recordGapCenter - 232822).Prime := by
  rw [fullRecordGapTerm02586_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02586, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02586_fast_pow_mod_ne_one

def fullRecordGapValue02587 : Nat := fullRecordGapCenterValue - 232612

theorem fullRecordGapTerm02587_eq_value :
    recordGapCenter - 232612 = fullRecordGapValue02587 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02587_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02587 (fullRecordGapValue02587 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02587_not_prime : ¬(recordGapCenter - 232612).Prime := by
  rw [fullRecordGapTerm02587_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02587, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02587_fast_pow_mod_ne_one

def fullRecordGapValue02588 : Nat := fullRecordGapCenterValue - 232444

theorem fullRecordGapTerm02588_eq_value :
    recordGapCenter - 232444 = fullRecordGapValue02588 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02588_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02588 (fullRecordGapValue02588 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02588_not_prime : ¬(recordGapCenter - 232444).Prime := by
  rw [fullRecordGapTerm02588_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02588, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02588_fast_pow_mod_ne_one

def fullRecordGapValue02589 : Nat := fullRecordGapCenterValue - 232402

theorem fullRecordGapTerm02589_eq_value :
    recordGapCenter - 232402 = fullRecordGapValue02589 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02589_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02589 (fullRecordGapValue02589 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02589_not_prime : ¬(recordGapCenter - 232402).Prime := by
  rw [fullRecordGapTerm02589_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02589, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02589_fast_pow_mod_ne_one

def fullRecordGapValue02590 : Nat := fullRecordGapCenterValue - 232378

theorem fullRecordGapTerm02590_eq_value :
    recordGapCenter - 232378 = fullRecordGapValue02590 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02590_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02590 (fullRecordGapValue02590 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02590_not_prime : ¬(recordGapCenter - 232378).Prime := by
  rw [fullRecordGapTerm02590_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02590, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02590_fast_pow_mod_ne_one

def fullRecordGapValue02591 : Nat := fullRecordGapCenterValue - 232320

theorem fullRecordGapTerm02591_eq_value :
    recordGapCenter - 232320 = fullRecordGapValue02591 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02591_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02591 (fullRecordGapValue02591 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02591_not_prime : ¬(recordGapCenter - 232320).Prime := by
  rw [fullRecordGapTerm02591_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02591, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02591_fast_pow_mod_ne_one

def fullRecordGapValue02592 : Nat := fullRecordGapCenterValue - 232054

theorem fullRecordGapTerm02592_eq_value :
    recordGapCenter - 232054 = fullRecordGapValue02592 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02592_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02592 (fullRecordGapValue02592 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02592_not_prime : ¬(recordGapCenter - 232054).Prime := by
  rw [fullRecordGapTerm02592_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02592, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02592_fast_pow_mod_ne_one

def fullRecordGapValue02593 : Nat := fullRecordGapCenterValue - 231964

theorem fullRecordGapTerm02593_eq_value :
    recordGapCenter - 231964 = fullRecordGapValue02593 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02593_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02593 (fullRecordGapValue02593 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02593_not_prime : ¬(recordGapCenter - 231964).Prime := by
  rw [fullRecordGapTerm02593_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02593, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02593_fast_pow_mod_ne_one

def fullRecordGapValue02594 : Nat := fullRecordGapCenterValue - 231892

theorem fullRecordGapTerm02594_eq_value :
    recordGapCenter - 231892 = fullRecordGapValue02594 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02594_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02594 (fullRecordGapValue02594 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02594_not_prime : ¬(recordGapCenter - 231892).Prime := by
  rw [fullRecordGapTerm02594_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02594, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02594_fast_pow_mod_ne_one

def fullRecordGapValue02595 : Nat := fullRecordGapCenterValue - 231802

theorem fullRecordGapTerm02595_eq_value :
    recordGapCenter - 231802 = fullRecordGapValue02595 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02595_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02595 (fullRecordGapValue02595 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02595_not_prime : ¬(recordGapCenter - 231802).Prime := by
  rw [fullRecordGapTerm02595_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02595, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02595_fast_pow_mod_ne_one

def fullRecordGapValue02596 : Nat := fullRecordGapCenterValue - 231772

theorem fullRecordGapTerm02596_eq_value :
    recordGapCenter - 231772 = fullRecordGapValue02596 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02596_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02596 (fullRecordGapValue02596 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02596_not_prime : ¬(recordGapCenter - 231772).Prime := by
  rw [fullRecordGapTerm02596_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02596, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02596_fast_pow_mod_ne_one

def fullRecordGapValue02597 : Nat := fullRecordGapCenterValue - 231754

theorem fullRecordGapTerm02597_eq_value :
    recordGapCenter - 231754 = fullRecordGapValue02597 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02597_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02597 (fullRecordGapValue02597 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02597_not_prime : ¬(recordGapCenter - 231754).Prime := by
  rw [fullRecordGapTerm02597_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02597, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02597_fast_pow_mod_ne_one

def fullRecordGapValue02598 : Nat := fullRecordGapCenterValue - 231718

theorem fullRecordGapTerm02598_eq_value :
    recordGapCenter - 231718 = fullRecordGapValue02598 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02598_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02598 (fullRecordGapValue02598 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02598_not_prime : ¬(recordGapCenter - 231718).Prime := by
  rw [fullRecordGapTerm02598_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02598, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02598_fast_pow_mod_ne_one

def fullRecordGapValue02599 : Nat := fullRecordGapCenterValue - 231622

theorem fullRecordGapTerm02599_eq_value :
    recordGapCenter - 231622 = fullRecordGapValue02599 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02599_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02599 (fullRecordGapValue02599 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02599_not_prime : ¬(recordGapCenter - 231622).Prime := by
  rw [fullRecordGapTerm02599_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02599, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02599_fast_pow_mod_ne_one

def fullRecordGapValue02600 : Nat := fullRecordGapCenterValue - 231604

theorem fullRecordGapTerm02600_eq_value :
    recordGapCenter - 231604 = fullRecordGapValue02600 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02600_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02600 (fullRecordGapValue02600 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02600_not_prime : ¬(recordGapCenter - 231604).Prime := by
  rw [fullRecordGapTerm02600_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02600, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02600_fast_pow_mod_ne_one

def fullRecordGapValue02601 : Nat := fullRecordGapCenterValue - 231562

theorem fullRecordGapTerm02601_eq_value :
    recordGapCenter - 231562 = fullRecordGapValue02601 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02601_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02601 (fullRecordGapValue02601 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02601_not_prime : ¬(recordGapCenter - 231562).Prime := by
  rw [fullRecordGapTerm02601_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02601, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02601_fast_pow_mod_ne_one

def fullRecordGapValue02602 : Nat := fullRecordGapCenterValue - 231454

theorem fullRecordGapTerm02602_eq_value :
    recordGapCenter - 231454 = fullRecordGapValue02602 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02602_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02602 (fullRecordGapValue02602 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02602_not_prime : ¬(recordGapCenter - 231454).Prime := by
  rw [fullRecordGapTerm02602_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02602, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02602_fast_pow_mod_ne_one

def fullRecordGapValue02603 : Nat := fullRecordGapCenterValue - 231412

theorem fullRecordGapTerm02603_eq_value :
    recordGapCenter - 231412 = fullRecordGapValue02603 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02603_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02603 (fullRecordGapValue02603 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02603_not_prime : ¬(recordGapCenter - 231412).Prime := by
  rw [fullRecordGapTerm02603_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02603, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02603_fast_pow_mod_ne_one

def fullRecordGapValue02604 : Nat := fullRecordGapCenterValue - 231388

theorem fullRecordGapTerm02604_eq_value :
    recordGapCenter - 231388 = fullRecordGapValue02604 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02604_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02604 (fullRecordGapValue02604 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02604_not_prime : ¬(recordGapCenter - 231388).Prime := by
  rw [fullRecordGapTerm02604_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02604, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02604_fast_pow_mod_ne_one

def fullRecordGapValue02605 : Nat := fullRecordGapCenterValue - 231178

theorem fullRecordGapTerm02605_eq_value :
    recordGapCenter - 231178 = fullRecordGapValue02605 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02605_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02605 (fullRecordGapValue02605 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02605_not_prime : ¬(recordGapCenter - 231178).Prime := by
  rw [fullRecordGapTerm02605_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02605, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02605_fast_pow_mod_ne_one

def fullRecordGapValue02606 : Nat := fullRecordGapCenterValue - 231172

theorem fullRecordGapTerm02606_eq_value :
    recordGapCenter - 231172 = fullRecordGapValue02606 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02606_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02606 (fullRecordGapValue02606 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02606_not_prime : ¬(recordGapCenter - 231172).Prime := by
  rw [fullRecordGapTerm02606_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02606, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02606_fast_pow_mod_ne_one

def fullRecordGapValue02607 : Nat := fullRecordGapCenterValue - 231142

theorem fullRecordGapTerm02607_eq_value :
    recordGapCenter - 231142 = fullRecordGapValue02607 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02607_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02607 (fullRecordGapValue02607 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02607_not_prime : ¬(recordGapCenter - 231142).Prime := by
  rw [fullRecordGapTerm02607_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02607, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02607_fast_pow_mod_ne_one

def fullRecordGapValue02608 : Nat := fullRecordGapCenterValue - 231094

theorem fullRecordGapTerm02608_eq_value :
    recordGapCenter - 231094 = fullRecordGapValue02608 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02608_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02608 (fullRecordGapValue02608 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02608_not_prime : ¬(recordGapCenter - 231094).Prime := by
  rw [fullRecordGapTerm02608_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02608, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02608_fast_pow_mod_ne_one

def fullRecordGapValue02609 : Nat := fullRecordGapCenterValue - 230638

theorem fullRecordGapTerm02609_eq_value :
    recordGapCenter - 230638 = fullRecordGapValue02609 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02609_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02609 (fullRecordGapValue02609 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02609_not_prime : ¬(recordGapCenter - 230638).Prime := by
  rw [fullRecordGapTerm02609_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02609, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02609_fast_pow_mod_ne_one

def fullRecordGapValue02610 : Nat := fullRecordGapCenterValue - 230302

theorem fullRecordGapTerm02610_eq_value :
    recordGapCenter - 230302 = fullRecordGapValue02610 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02610_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02610 (fullRecordGapValue02610 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02610_not_prime : ¬(recordGapCenter - 230302).Prime := by
  rw [fullRecordGapTerm02610_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02610, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02610_fast_pow_mod_ne_one

def fullRecordGapValue02611 : Nat := fullRecordGapCenterValue - 230134

theorem fullRecordGapTerm02611_eq_value :
    recordGapCenter - 230134 = fullRecordGapValue02611 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02611_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02611 (fullRecordGapValue02611 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02611_not_prime : ¬(recordGapCenter - 230134).Prime := by
  rw [fullRecordGapTerm02611_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02611, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02611_fast_pow_mod_ne_one

def fullRecordGapValue02612 : Nat := fullRecordGapCenterValue - 229654

theorem fullRecordGapTerm02612_eq_value :
    recordGapCenter - 229654 = fullRecordGapValue02612 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02612_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02612 (fullRecordGapValue02612 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02612_not_prime : ¬(recordGapCenter - 229654).Prime := by
  rw [fullRecordGapTerm02612_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02612, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02612_fast_pow_mod_ne_one

def fullRecordGapValue02613 : Nat := fullRecordGapCenterValue - 229324

theorem fullRecordGapTerm02613_eq_value :
    recordGapCenter - 229324 = fullRecordGapValue02613 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02613_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02613 (fullRecordGapValue02613 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02613_not_prime : ¬(recordGapCenter - 229324).Prime := by
  rw [fullRecordGapTerm02613_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02613, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02613_fast_pow_mod_ne_one

def fullRecordGapValue02614 : Nat := fullRecordGapCenterValue - 229198

theorem fullRecordGapTerm02614_eq_value :
    recordGapCenter - 229198 = fullRecordGapValue02614 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02614_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02614 (fullRecordGapValue02614 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02614_not_prime : ¬(recordGapCenter - 229198).Prime := by
  rw [fullRecordGapTerm02614_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02614, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02614_fast_pow_mod_ne_one

def fullRecordGapValue02615 : Nat := fullRecordGapCenterValue - 228934

theorem fullRecordGapTerm02615_eq_value :
    recordGapCenter - 228934 = fullRecordGapValue02615 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02615_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02615 (fullRecordGapValue02615 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02615_not_prime : ¬(recordGapCenter - 228934).Prime := by
  rw [fullRecordGapTerm02615_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02615, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02615_fast_pow_mod_ne_one

def fullRecordGapValue02616 : Nat := fullRecordGapCenterValue - 228690

theorem fullRecordGapTerm02616_eq_value :
    recordGapCenter - 228690 = fullRecordGapValue02616 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02616_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02616 (fullRecordGapValue02616 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02616_not_prime : ¬(recordGapCenter - 228690).Prime := by
  rw [fullRecordGapTerm02616_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02616, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02616_fast_pow_mod_ne_one

def fullRecordGapValue02617 : Nat := fullRecordGapCenterValue - 228658

theorem fullRecordGapTerm02617_eq_value :
    recordGapCenter - 228658 = fullRecordGapValue02617 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02617_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02617 (fullRecordGapValue02617 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02617_not_prime : ¬(recordGapCenter - 228658).Prime := by
  rw [fullRecordGapTerm02617_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02617, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02617_fast_pow_mod_ne_one

def fullRecordGapValue02618 : Nat := fullRecordGapCenterValue - 228622

theorem fullRecordGapTerm02618_eq_value :
    recordGapCenter - 228622 = fullRecordGapValue02618 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02618_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02618 (fullRecordGapValue02618 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02618_not_prime : ¬(recordGapCenter - 228622).Prime := by
  rw [fullRecordGapTerm02618_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02618, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02618_fast_pow_mod_ne_one

def fullRecordGapValue02619 : Nat := fullRecordGapCenterValue - 228598

theorem fullRecordGapTerm02619_eq_value :
    recordGapCenter - 228598 = fullRecordGapValue02619 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02619_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02619 (fullRecordGapValue02619 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02619_not_prime : ¬(recordGapCenter - 228598).Prime := by
  rw [fullRecordGapTerm02619_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02619, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02619_fast_pow_mod_ne_one

def fullRecordGapValue02620 : Nat := fullRecordGapCenterValue - 228442

theorem fullRecordGapTerm02620_eq_value :
    recordGapCenter - 228442 = fullRecordGapValue02620 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02620_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02620 (fullRecordGapValue02620 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02620_not_prime : ¬(recordGapCenter - 228442).Prime := by
  rw [fullRecordGapTerm02620_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02620, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02620_fast_pow_mod_ne_one

def fullRecordGapValue02621 : Nat := fullRecordGapCenterValue - 228388

theorem fullRecordGapTerm02621_eq_value :
    recordGapCenter - 228388 = fullRecordGapValue02621 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02621_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02621 (fullRecordGapValue02621 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02621_not_prime : ¬(recordGapCenter - 228388).Prime := by
  rw [fullRecordGapTerm02621_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02621, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02621_fast_pow_mod_ne_one

def fullRecordGapValue02622 : Nat := fullRecordGapCenterValue - 228322

theorem fullRecordGapTerm02622_eq_value :
    recordGapCenter - 228322 = fullRecordGapValue02622 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02622_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02622 (fullRecordGapValue02622 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02622_not_prime : ¬(recordGapCenter - 228322).Prime := by
  rw [fullRecordGapTerm02622_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02622, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02622_fast_pow_mod_ne_one

def fullRecordGapValue02623 : Nat := fullRecordGapCenterValue - 227938

theorem fullRecordGapTerm02623_eq_value :
    recordGapCenter - 227938 = fullRecordGapValue02623 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02623_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02623 (fullRecordGapValue02623 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02623_not_prime : ¬(recordGapCenter - 227938).Prime := by
  rw [fullRecordGapTerm02623_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02623, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02623_fast_pow_mod_ne_one

def fullRecordGapValue02624 : Nat := fullRecordGapCenterValue - 227782

theorem fullRecordGapTerm02624_eq_value :
    recordGapCenter - 227782 = fullRecordGapValue02624 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02624_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02624 (fullRecordGapValue02624 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02624_not_prime : ¬(recordGapCenter - 227782).Prime := by
  rw [fullRecordGapTerm02624_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02624, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02624_fast_pow_mod_ne_one

def fullRecordGapValue02625 : Nat := fullRecordGapCenterValue - 227692

theorem fullRecordGapTerm02625_eq_value :
    recordGapCenter - 227692 = fullRecordGapValue02625 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02625_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02625 (fullRecordGapValue02625 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02625_not_prime : ¬(recordGapCenter - 227692).Prime := by
  rw [fullRecordGapTerm02625_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02625, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02625_fast_pow_mod_ne_one

def fullRecordGapValue02626 : Nat := fullRecordGapCenterValue - 227674

theorem fullRecordGapTerm02626_eq_value :
    recordGapCenter - 227674 = fullRecordGapValue02626 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02626_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02626 (fullRecordGapValue02626 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02626_not_prime : ¬(recordGapCenter - 227674).Prime := by
  rw [fullRecordGapTerm02626_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02626, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02626_fast_pow_mod_ne_one

def fullRecordGapValue02627 : Nat := fullRecordGapCenterValue - 227434

theorem fullRecordGapTerm02627_eq_value :
    recordGapCenter - 227434 = fullRecordGapValue02627 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02627_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02627 (fullRecordGapValue02627 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02627_not_prime : ¬(recordGapCenter - 227434).Prime := by
  rw [fullRecordGapTerm02627_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02627, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02627_fast_pow_mod_ne_one

def fullRecordGapValue02628 : Nat := fullRecordGapCenterValue - 227428

theorem fullRecordGapTerm02628_eq_value :
    recordGapCenter - 227428 = fullRecordGapValue02628 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02628_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02628 (fullRecordGapValue02628 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02628_not_prime : ¬(recordGapCenter - 227428).Prime := by
  rw [fullRecordGapTerm02628_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02628, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02628_fast_pow_mod_ne_one

def fullRecordGapValue02629 : Nat := fullRecordGapCenterValue - 227182

theorem fullRecordGapTerm02629_eq_value :
    recordGapCenter - 227182 = fullRecordGapValue02629 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02629_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02629 (fullRecordGapValue02629 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02629_not_prime : ¬(recordGapCenter - 227182).Prime := by
  rw [fullRecordGapTerm02629_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02629, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02629_fast_pow_mod_ne_one

def fullRecordGapValue02630 : Nat := fullRecordGapCenterValue - 227134

theorem fullRecordGapTerm02630_eq_value :
    recordGapCenter - 227134 = fullRecordGapValue02630 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02630_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02630 (fullRecordGapValue02630 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02630_not_prime : ¬(recordGapCenter - 227134).Prime := by
  rw [fullRecordGapTerm02630_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02630, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02630_fast_pow_mod_ne_one

def fullRecordGapValue02631 : Nat := fullRecordGapCenterValue - 227092

theorem fullRecordGapTerm02631_eq_value :
    recordGapCenter - 227092 = fullRecordGapValue02631 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02631_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02631 (fullRecordGapValue02631 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02631_not_prime : ¬(recordGapCenter - 227092).Prime := by
  rw [fullRecordGapTerm02631_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02631, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02631_fast_pow_mod_ne_one

def fullRecordGapValue02632 : Nat := fullRecordGapCenterValue - 227068

theorem fullRecordGapTerm02632_eq_value :
    recordGapCenter - 227068 = fullRecordGapValue02632 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02632_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02632 (fullRecordGapValue02632 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02632_not_prime : ¬(recordGapCenter - 227068).Prime := by
  rw [fullRecordGapTerm02632_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02632, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02632_fast_pow_mod_ne_one

def fullRecordGapValue02633 : Nat := fullRecordGapCenterValue - 227002

theorem fullRecordGapTerm02633_eq_value :
    recordGapCenter - 227002 = fullRecordGapValue02633 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02633_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02633 (fullRecordGapValue02633 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02633_not_prime : ¬(recordGapCenter - 227002).Prime := by
  rw [fullRecordGapTerm02633_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02633, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02633_fast_pow_mod_ne_one

def fullRecordGapValue02634 : Nat := fullRecordGapCenterValue - 226558

theorem fullRecordGapTerm02634_eq_value :
    recordGapCenter - 226558 = fullRecordGapValue02634 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02634_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02634 (fullRecordGapValue02634 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02634_not_prime : ¬(recordGapCenter - 226558).Prime := by
  rw [fullRecordGapTerm02634_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02634, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02634_fast_pow_mod_ne_one

def fullRecordGapValue02635 : Nat := fullRecordGapCenterValue - 226294

theorem fullRecordGapTerm02635_eq_value :
    recordGapCenter - 226294 = fullRecordGapValue02635 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02635_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02635 (fullRecordGapValue02635 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02635_not_prime : ¬(recordGapCenter - 226294).Prime := by
  rw [fullRecordGapTerm02635_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02635, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02635_fast_pow_mod_ne_one

def fullRecordGapValue02636 : Nat := fullRecordGapCenterValue - 226222

theorem fullRecordGapTerm02636_eq_value :
    recordGapCenter - 226222 = fullRecordGapValue02636 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02636_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02636 (fullRecordGapValue02636 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02636_not_prime : ¬(recordGapCenter - 226222).Prime := by
  rw [fullRecordGapTerm02636_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02636, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02636_fast_pow_mod_ne_one

def fullRecordGapValue02637 : Nat := fullRecordGapCenterValue - 226162

theorem fullRecordGapTerm02637_eq_value :
    recordGapCenter - 226162 = fullRecordGapValue02637 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02637_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02637 (fullRecordGapValue02637 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02637_not_prime : ¬(recordGapCenter - 226162).Prime := by
  rw [fullRecordGapTerm02637_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02637, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02637_fast_pow_mod_ne_one

def fullRecordGapValue02638 : Nat := fullRecordGapCenterValue - 226102

theorem fullRecordGapTerm02638_eq_value :
    recordGapCenter - 226102 = fullRecordGapValue02638 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02638_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02638 (fullRecordGapValue02638 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02638_not_prime : ¬(recordGapCenter - 226102).Prime := by
  rw [fullRecordGapTerm02638_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02638, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02638_fast_pow_mod_ne_one

def fullRecordGapValue02639 : Nat := fullRecordGapCenterValue - 226078

theorem fullRecordGapTerm02639_eq_value :
    recordGapCenter - 226078 = fullRecordGapValue02639 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02639_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02639 (fullRecordGapValue02639 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02639_not_prime : ¬(recordGapCenter - 226078).Prime := by
  rw [fullRecordGapTerm02639_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02639, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02639_fast_pow_mod_ne_one

def fullRecordGapValue02640 : Nat := fullRecordGapCenterValue - 226042

theorem fullRecordGapTerm02640_eq_value :
    recordGapCenter - 226042 = fullRecordGapValue02640 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02640_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02640 (fullRecordGapValue02640 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02640_not_prime : ¬(recordGapCenter - 226042).Prime := by
  rw [fullRecordGapTerm02640_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02640, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02640_fast_pow_mod_ne_one

def fullRecordGapValue02641 : Nat := fullRecordGapCenterValue - 226012

theorem fullRecordGapTerm02641_eq_value :
    recordGapCenter - 226012 = fullRecordGapValue02641 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02641_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02641 (fullRecordGapValue02641 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02641_not_prime : ¬(recordGapCenter - 226012).Prime := by
  rw [fullRecordGapTerm02641_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02641, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02641_fast_pow_mod_ne_one

def fullRecordGapValue02642 : Nat := fullRecordGapCenterValue - 225994

theorem fullRecordGapTerm02642_eq_value :
    recordGapCenter - 225994 = fullRecordGapValue02642 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02642_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02642 (fullRecordGapValue02642 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02642_not_prime : ¬(recordGapCenter - 225994).Prime := by
  rw [fullRecordGapTerm02642_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02642, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02642_fast_pow_mod_ne_one

def fullRecordGapValue02643 : Nat := fullRecordGapCenterValue - 225868

theorem fullRecordGapTerm02643_eq_value :
    recordGapCenter - 225868 = fullRecordGapValue02643 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02643_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02643 (fullRecordGapValue02643 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02643_not_prime : ¬(recordGapCenter - 225868).Prime := by
  rw [fullRecordGapTerm02643_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02643, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02643_fast_pow_mod_ne_one

def fullRecordGapValue02644 : Nat := fullRecordGapCenterValue - 225748

theorem fullRecordGapTerm02644_eq_value :
    recordGapCenter - 225748 = fullRecordGapValue02644 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02644_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02644 (fullRecordGapValue02644 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02644_not_prime : ¬(recordGapCenter - 225748).Prime := by
  rw [fullRecordGapTerm02644_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02644, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02644_fast_pow_mod_ne_one

def fullRecordGapValue02645 : Nat := fullRecordGapCenterValue - 225718

theorem fullRecordGapTerm02645_eq_value :
    recordGapCenter - 225718 = fullRecordGapValue02645 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02645_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02645 (fullRecordGapValue02645 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02645_not_prime : ¬(recordGapCenter - 225718).Prime := by
  rw [fullRecordGapTerm02645_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02645, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02645_fast_pow_mod_ne_one

def fullRecordGapValue02646 : Nat := fullRecordGapCenterValue - 225598

theorem fullRecordGapTerm02646_eq_value :
    recordGapCenter - 225598 = fullRecordGapValue02646 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02646_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02646 (fullRecordGapValue02646 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02646_not_prime : ¬(recordGapCenter - 225598).Prime := by
  rw [fullRecordGapTerm02646_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02646, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02646_fast_pow_mod_ne_one

def fullRecordGapValue02647 : Nat := fullRecordGapCenterValue - 225532

theorem fullRecordGapTerm02647_eq_value :
    recordGapCenter - 225532 = fullRecordGapValue02647 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02647_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02647 (fullRecordGapValue02647 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02647_not_prime : ¬(recordGapCenter - 225532).Prime := by
  rw [fullRecordGapTerm02647_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02647, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02647_fast_pow_mod_ne_one

def fullRecordGapValue02648 : Nat := fullRecordGapCenterValue - 225514

theorem fullRecordGapTerm02648_eq_value :
    recordGapCenter - 225514 = fullRecordGapValue02648 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02648_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02648 (fullRecordGapValue02648 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02648_not_prime : ¬(recordGapCenter - 225514).Prime := by
  rw [fullRecordGapTerm02648_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02648, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02648_fast_pow_mod_ne_one

def fullRecordGapValue02649 : Nat := fullRecordGapCenterValue - 225154

theorem fullRecordGapTerm02649_eq_value :
    recordGapCenter - 225154 = fullRecordGapValue02649 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02649_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02649 (fullRecordGapValue02649 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02649_not_prime : ¬(recordGapCenter - 225154).Prime := by
  rw [fullRecordGapTerm02649_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02649, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02649_fast_pow_mod_ne_one

def fullRecordGapValue02650 : Nat := fullRecordGapCenterValue - 225118

theorem fullRecordGapTerm02650_eq_value :
    recordGapCenter - 225118 = fullRecordGapValue02650 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02650_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02650 (fullRecordGapValue02650 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02650_not_prime : ¬(recordGapCenter - 225118).Prime := by
  rw [fullRecordGapTerm02650_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02650, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02650_fast_pow_mod_ne_one

def fullRecordGapValue02651 : Nat := fullRecordGapCenterValue - 225000

theorem fullRecordGapTerm02651_eq_value :
    recordGapCenter - 225000 = fullRecordGapValue02651 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02651_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02651 (fullRecordGapValue02651 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02651_not_prime : ¬(recordGapCenter - 225000).Prime := by
  rw [fullRecordGapTerm02651_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02651, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02651_fast_pow_mod_ne_one

def fullRecordGapValue02652 : Nat := fullRecordGapCenterValue - 224788

theorem fullRecordGapTerm02652_eq_value :
    recordGapCenter - 224788 = fullRecordGapValue02652 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02652_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02652 (fullRecordGapValue02652 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02652_not_prime : ¬(recordGapCenter - 224788).Prime := by
  rw [fullRecordGapTerm02652_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02652, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02652_fast_pow_mod_ne_one

def fullRecordGapValue02653 : Nat := fullRecordGapCenterValue - 224674

theorem fullRecordGapTerm02653_eq_value :
    recordGapCenter - 224674 = fullRecordGapValue02653 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02653_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02653 (fullRecordGapValue02653 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02653_not_prime : ¬(recordGapCenter - 224674).Prime := by
  rw [fullRecordGapTerm02653_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02653, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02653_fast_pow_mod_ne_one

def fullRecordGapValue02654 : Nat := fullRecordGapCenterValue - 224662

theorem fullRecordGapTerm02654_eq_value :
    recordGapCenter - 224662 = fullRecordGapValue02654 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02654_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02654 (fullRecordGapValue02654 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02654_not_prime : ¬(recordGapCenter - 224662).Prime := by
  rw [fullRecordGapTerm02654_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02654, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02654_fast_pow_mod_ne_one

def fullRecordGapValue02655 : Nat := fullRecordGapCenterValue - 224524

theorem fullRecordGapTerm02655_eq_value :
    recordGapCenter - 224524 = fullRecordGapValue02655 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02655_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02655 (fullRecordGapValue02655 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02655_not_prime : ¬(recordGapCenter - 224524).Prime := by
  rw [fullRecordGapTerm02655_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02655, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02655_fast_pow_mod_ne_one

def fullRecordGapValue02656 : Nat := fullRecordGapCenterValue - 224494

theorem fullRecordGapTerm02656_eq_value :
    recordGapCenter - 224494 = fullRecordGapValue02656 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02656_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02656 (fullRecordGapValue02656 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02656_not_prime : ¬(recordGapCenter - 224494).Prime := by
  rw [fullRecordGapTerm02656_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02656, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02656_fast_pow_mod_ne_one

def fullRecordGapValue02657 : Nat := fullRecordGapCenterValue - 224398

theorem fullRecordGapTerm02657_eq_value :
    recordGapCenter - 224398 = fullRecordGapValue02657 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02657_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02657 (fullRecordGapValue02657 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02657_not_prime : ¬(recordGapCenter - 224398).Prime := by
  rw [fullRecordGapTerm02657_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02657, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02657_fast_pow_mod_ne_one

def fullRecordGapValue02658 : Nat := fullRecordGapCenterValue - 224362

theorem fullRecordGapTerm02658_eq_value :
    recordGapCenter - 224362 = fullRecordGapValue02658 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02658_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02658 (fullRecordGapValue02658 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02658_not_prime : ¬(recordGapCenter - 224362).Prime := by
  rw [fullRecordGapTerm02658_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02658, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02658_fast_pow_mod_ne_one

def fullRecordGapValue02659 : Nat := fullRecordGapCenterValue - 224278

theorem fullRecordGapTerm02659_eq_value :
    recordGapCenter - 224278 = fullRecordGapValue02659 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02659_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02659 (fullRecordGapValue02659 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02659_not_prime : ¬(recordGapCenter - 224278).Prime := by
  rw [fullRecordGapTerm02659_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02659, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02659_fast_pow_mod_ne_one

def fullRecordGapValue02660 : Nat := fullRecordGapCenterValue - 224212

theorem fullRecordGapTerm02660_eq_value :
    recordGapCenter - 224212 = fullRecordGapValue02660 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02660_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02660 (fullRecordGapValue02660 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02660_not_prime : ¬(recordGapCenter - 224212).Prime := by
  rw [fullRecordGapTerm02660_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02660, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02660_fast_pow_mod_ne_one

def fullRecordGapValue02661 : Nat := fullRecordGapCenterValue - 224194

theorem fullRecordGapTerm02661_eq_value :
    recordGapCenter - 224194 = fullRecordGapValue02661 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02661_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02661 (fullRecordGapValue02661 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02661_not_prime : ¬(recordGapCenter - 224194).Prime := by
  rw [fullRecordGapTerm02661_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02661, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02661_fast_pow_mod_ne_one

def fullRecordGapValue02662 : Nat := fullRecordGapCenterValue - 224164

theorem fullRecordGapTerm02662_eq_value :
    recordGapCenter - 224164 = fullRecordGapValue02662 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02662_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02662 (fullRecordGapValue02662 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02662_not_prime : ¬(recordGapCenter - 224164).Prime := by
  rw [fullRecordGapTerm02662_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02662, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02662_fast_pow_mod_ne_one

def fullRecordGapValue02663 : Nat := fullRecordGapCenterValue - 224038

theorem fullRecordGapTerm02663_eq_value :
    recordGapCenter - 224038 = fullRecordGapValue02663 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02663_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02663 (fullRecordGapValue02663 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02663_not_prime : ¬(recordGapCenter - 224038).Prime := by
  rw [fullRecordGapTerm02663_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02663, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02663_fast_pow_mod_ne_one

def fullRecordGapValue02664 : Nat := fullRecordGapCenterValue - 223918

theorem fullRecordGapTerm02664_eq_value :
    recordGapCenter - 223918 = fullRecordGapValue02664 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02664_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02664 (fullRecordGapValue02664 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02664_not_prime : ¬(recordGapCenter - 223918).Prime := by
  rw [fullRecordGapTerm02664_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02664, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02664_fast_pow_mod_ne_one

def fullRecordGapValue02665 : Nat := fullRecordGapCenterValue - 223732

theorem fullRecordGapTerm02665_eq_value :
    recordGapCenter - 223732 = fullRecordGapValue02665 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02665_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02665 (fullRecordGapValue02665 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02665_not_prime : ¬(recordGapCenter - 223732).Prime := by
  rw [fullRecordGapTerm02665_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02665, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02665_fast_pow_mod_ne_one

def fullRecordGapValue02666 : Nat := fullRecordGapCenterValue - 223654

theorem fullRecordGapTerm02666_eq_value :
    recordGapCenter - 223654 = fullRecordGapValue02666 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02666_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02666 (fullRecordGapValue02666 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02666_not_prime : ¬(recordGapCenter - 223654).Prime := by
  rw [fullRecordGapTerm02666_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02666, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02666_fast_pow_mod_ne_one

def fullRecordGapValue02667 : Nat := fullRecordGapCenterValue - 223582

theorem fullRecordGapTerm02667_eq_value :
    recordGapCenter - 223582 = fullRecordGapValue02667 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02667_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02667 (fullRecordGapValue02667 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02667_not_prime : ¬(recordGapCenter - 223582).Prime := by
  rw [fullRecordGapTerm02667_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02667, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02667_fast_pow_mod_ne_one

def fullRecordGapValue02668 : Nat := fullRecordGapCenterValue - 223318

theorem fullRecordGapTerm02668_eq_value :
    recordGapCenter - 223318 = fullRecordGapValue02668 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02668_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02668 (fullRecordGapValue02668 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02668_not_prime : ¬(recordGapCenter - 223318).Prime := by
  rw [fullRecordGapTerm02668_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02668, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02668_fast_pow_mod_ne_one

def fullRecordGapValue02669 : Nat := fullRecordGapCenterValue - 223228

theorem fullRecordGapTerm02669_eq_value :
    recordGapCenter - 223228 = fullRecordGapValue02669 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02669_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02669 (fullRecordGapValue02669 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02669_not_prime : ¬(recordGapCenter - 223228).Prime := by
  rw [fullRecordGapTerm02669_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02669, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02669_fast_pow_mod_ne_one

def fullRecordGapValue02670 : Nat := fullRecordGapCenterValue - 223078

theorem fullRecordGapTerm02670_eq_value :
    recordGapCenter - 223078 = fullRecordGapValue02670 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02670_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02670 (fullRecordGapValue02670 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02670_not_prime : ¬(recordGapCenter - 223078).Prime := by
  rw [fullRecordGapTerm02670_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02670, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02670_fast_pow_mod_ne_one

def fullRecordGapValue02671 : Nat := fullRecordGapCenterValue - 222934

theorem fullRecordGapTerm02671_eq_value :
    recordGapCenter - 222934 = fullRecordGapValue02671 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02671_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02671 (fullRecordGapValue02671 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02671_not_prime : ¬(recordGapCenter - 222934).Prime := by
  rw [fullRecordGapTerm02671_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02671, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02671_fast_pow_mod_ne_one

def fullRecordGapValue02672 : Nat := fullRecordGapCenterValue - 222862

theorem fullRecordGapTerm02672_eq_value :
    recordGapCenter - 222862 = fullRecordGapValue02672 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02672_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02672 (fullRecordGapValue02672 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02672_not_prime : ¬(recordGapCenter - 222862).Prime := by
  rw [fullRecordGapTerm02672_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02672, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02672_fast_pow_mod_ne_one

def fullRecordGapValue02673 : Nat := fullRecordGapCenterValue - 222694

theorem fullRecordGapTerm02673_eq_value :
    recordGapCenter - 222694 = fullRecordGapValue02673 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02673_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02673 (fullRecordGapValue02673 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02673_not_prime : ¬(recordGapCenter - 222694).Prime := by
  rw [fullRecordGapTerm02673_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02673, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02673_fast_pow_mod_ne_one

def fullRecordGapValue02674 : Nat := fullRecordGapCenterValue - 222652

theorem fullRecordGapTerm02674_eq_value :
    recordGapCenter - 222652 = fullRecordGapValue02674 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02674_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02674 (fullRecordGapValue02674 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02674_not_prime : ¬(recordGapCenter - 222652).Prime := by
  rw [fullRecordGapTerm02674_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02674, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02674_fast_pow_mod_ne_one

def fullRecordGapValue02675 : Nat := fullRecordGapCenterValue - 222532

theorem fullRecordGapTerm02675_eq_value :
    recordGapCenter - 222532 = fullRecordGapValue02675 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02675_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02675 (fullRecordGapValue02675 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02675_not_prime : ¬(recordGapCenter - 222532).Prime := by
  rw [fullRecordGapTerm02675_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02675, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02675_fast_pow_mod_ne_one

def fullRecordGapValue02676 : Nat := fullRecordGapCenterValue - 222484

theorem fullRecordGapTerm02676_eq_value :
    recordGapCenter - 222484 = fullRecordGapValue02676 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02676_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02676 (fullRecordGapValue02676 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02676_not_prime : ¬(recordGapCenter - 222484).Prime := by
  rw [fullRecordGapTerm02676_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02676, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02676_fast_pow_mod_ne_one

def fullRecordGapValue02677 : Nat := fullRecordGapCenterValue - 222238

theorem fullRecordGapTerm02677_eq_value :
    recordGapCenter - 222238 = fullRecordGapValue02677 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02677_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02677 (fullRecordGapValue02677 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02677_not_prime : ¬(recordGapCenter - 222238).Prime := by
  rw [fullRecordGapTerm02677_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02677, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02677_fast_pow_mod_ne_one

def fullRecordGapValue02678 : Nat := fullRecordGapCenterValue - 222058

theorem fullRecordGapTerm02678_eq_value :
    recordGapCenter - 222058 = fullRecordGapValue02678 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02678_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02678 (fullRecordGapValue02678 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02678_not_prime : ¬(recordGapCenter - 222058).Prime := by
  rw [fullRecordGapTerm02678_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02678, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02678_fast_pow_mod_ne_one

def fullRecordGapValue02679 : Nat := fullRecordGapCenterValue - 222004

theorem fullRecordGapTerm02679_eq_value :
    recordGapCenter - 222004 = fullRecordGapValue02679 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02679_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02679 (fullRecordGapValue02679 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02679_not_prime : ¬(recordGapCenter - 222004).Prime := by
  rw [fullRecordGapTerm02679_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02679, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02679_fast_pow_mod_ne_one

def fullRecordGapValue02680 : Nat := fullRecordGapCenterValue - 221902

theorem fullRecordGapTerm02680_eq_value :
    recordGapCenter - 221902 = fullRecordGapValue02680 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02680_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02680 (fullRecordGapValue02680 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02680_not_prime : ¬(recordGapCenter - 221902).Prime := by
  rw [fullRecordGapTerm02680_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02680, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02680_fast_pow_mod_ne_one

def fullRecordGapValue02681 : Nat := fullRecordGapCenterValue - 221842

theorem fullRecordGapTerm02681_eq_value :
    recordGapCenter - 221842 = fullRecordGapValue02681 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02681_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02681 (fullRecordGapValue02681 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02681_not_prime : ¬(recordGapCenter - 221842).Prime := by
  rw [fullRecordGapTerm02681_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02681, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02681_fast_pow_mod_ne_one

def fullRecordGapValue02682 : Nat := fullRecordGapCenterValue - 221758

theorem fullRecordGapTerm02682_eq_value :
    recordGapCenter - 221758 = fullRecordGapValue02682 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02682_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02682 (fullRecordGapValue02682 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02682_not_prime : ¬(recordGapCenter - 221758).Prime := by
  rw [fullRecordGapTerm02682_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02682, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02682_fast_pow_mod_ne_one

def fullRecordGapValue02683 : Nat := fullRecordGapCenterValue - 221644

theorem fullRecordGapTerm02683_eq_value :
    recordGapCenter - 221644 = fullRecordGapValue02683 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02683_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02683 (fullRecordGapValue02683 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02683_not_prime : ¬(recordGapCenter - 221644).Prime := by
  rw [fullRecordGapTerm02683_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02683, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02683_fast_pow_mod_ne_one

def fullRecordGapValue02684 : Nat := fullRecordGapCenterValue - 221458

theorem fullRecordGapTerm02684_eq_value :
    recordGapCenter - 221458 = fullRecordGapValue02684 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02684_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02684 (fullRecordGapValue02684 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02684_not_prime : ¬(recordGapCenter - 221458).Prime := by
  rw [fullRecordGapTerm02684_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02684, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02684_fast_pow_mod_ne_one

def fullRecordGapValue02685 : Nat := fullRecordGapCenterValue - 221332

theorem fullRecordGapTerm02685_eq_value :
    recordGapCenter - 221332 = fullRecordGapValue02685 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02685_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02685 (fullRecordGapValue02685 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02685_not_prime : ¬(recordGapCenter - 221332).Prime := by
  rw [fullRecordGapTerm02685_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02685, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02685_fast_pow_mod_ne_one

def fullRecordGapValue02686 : Nat := fullRecordGapCenterValue - 221218

theorem fullRecordGapTerm02686_eq_value :
    recordGapCenter - 221218 = fullRecordGapValue02686 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02686_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02686 (fullRecordGapValue02686 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02686_not_prime : ¬(recordGapCenter - 221218).Prime := by
  rw [fullRecordGapTerm02686_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02686, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02686_fast_pow_mod_ne_one

def fullRecordGapValue02687 : Nat := fullRecordGapCenterValue - 221164

theorem fullRecordGapTerm02687_eq_value :
    recordGapCenter - 221164 = fullRecordGapValue02687 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02687_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02687 (fullRecordGapValue02687 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02687_not_prime : ¬(recordGapCenter - 221164).Prime := by
  rw [fullRecordGapTerm02687_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02687, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02687_fast_pow_mod_ne_one

def fullRecordGapValue02688 : Nat := fullRecordGapCenterValue - 220882

theorem fullRecordGapTerm02688_eq_value :
    recordGapCenter - 220882 = fullRecordGapValue02688 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02688_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02688 (fullRecordGapValue02688 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02688_not_prime : ¬(recordGapCenter - 220882).Prime := by
  rw [fullRecordGapTerm02688_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02688, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02688_fast_pow_mod_ne_one

def fullRecordGapValue02689 : Nat := fullRecordGapCenterValue - 220828

theorem fullRecordGapTerm02689_eq_value :
    recordGapCenter - 220828 = fullRecordGapValue02689 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02689_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02689 (fullRecordGapValue02689 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02689_not_prime : ¬(recordGapCenter - 220828).Prime := by
  rw [fullRecordGapTerm02689_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02689, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02689_fast_pow_mod_ne_one

def fullRecordGapValue02690 : Nat := fullRecordGapCenterValue - 220678

theorem fullRecordGapTerm02690_eq_value :
    recordGapCenter - 220678 = fullRecordGapValue02690 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02690_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02690 (fullRecordGapValue02690 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02690_not_prime : ¬(recordGapCenter - 220678).Prime := by
  rw [fullRecordGapTerm02690_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02690, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02690_fast_pow_mod_ne_one

def fullRecordGapValue02691 : Nat := fullRecordGapCenterValue - 220468

theorem fullRecordGapTerm02691_eq_value :
    recordGapCenter - 220468 = fullRecordGapValue02691 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02691_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02691 (fullRecordGapValue02691 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02691_not_prime : ¬(recordGapCenter - 220468).Prime := by
  rw [fullRecordGapTerm02691_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02691, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02691_fast_pow_mod_ne_one

def fullRecordGapValue02692 : Nat := fullRecordGapCenterValue - 220138

theorem fullRecordGapTerm02692_eq_value :
    recordGapCenter - 220138 = fullRecordGapValue02692 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02692_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02692 (fullRecordGapValue02692 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02692_not_prime : ¬(recordGapCenter - 220138).Prime := by
  rw [fullRecordGapTerm02692_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02692, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02692_fast_pow_mod_ne_one

def fullRecordGapValue02693 : Nat := fullRecordGapCenterValue - 220084

theorem fullRecordGapTerm02693_eq_value :
    recordGapCenter - 220084 = fullRecordGapValue02693 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02693_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02693 (fullRecordGapValue02693 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02693_not_prime : ¬(recordGapCenter - 220084).Prime := by
  rw [fullRecordGapTerm02693_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02693, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02693_fast_pow_mod_ne_one

def fullRecordGapValue02694 : Nat := fullRecordGapCenterValue - 220078

theorem fullRecordGapTerm02694_eq_value :
    recordGapCenter - 220078 = fullRecordGapValue02694 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02694_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02694 (fullRecordGapValue02694 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02694_not_prime : ¬(recordGapCenter - 220078).Prime := by
  rw [fullRecordGapTerm02694_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02694, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02694_fast_pow_mod_ne_one

def fullRecordGapValue02695 : Nat := fullRecordGapCenterValue - 220000

theorem fullRecordGapTerm02695_eq_value :
    recordGapCenter - 220000 = fullRecordGapValue02695 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02695_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02695 (fullRecordGapValue02695 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02695_not_prime : ¬(recordGapCenter - 220000).Prime := by
  rw [fullRecordGapTerm02695_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02695, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02695_fast_pow_mod_ne_one

def fullRecordGapValue02696 : Nat := fullRecordGapCenterValue - 219874

theorem fullRecordGapTerm02696_eq_value :
    recordGapCenter - 219874 = fullRecordGapValue02696 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02696_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02696 (fullRecordGapValue02696 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02696_not_prime : ¬(recordGapCenter - 219874).Prime := by
  rw [fullRecordGapTerm02696_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02696, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02696_fast_pow_mod_ne_one

def fullRecordGapValue02697 : Nat := fullRecordGapCenterValue - 219694

theorem fullRecordGapTerm02697_eq_value :
    recordGapCenter - 219694 = fullRecordGapValue02697 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02697_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02697 (fullRecordGapValue02697 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02697_not_prime : ¬(recordGapCenter - 219694).Prime := by
  rw [fullRecordGapTerm02697_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02697, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02697_fast_pow_mod_ne_one

def fullRecordGapValue02698 : Nat := fullRecordGapCenterValue - 219658

theorem fullRecordGapTerm02698_eq_value :
    recordGapCenter - 219658 = fullRecordGapValue02698 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02698_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02698 (fullRecordGapValue02698 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02698_not_prime : ¬(recordGapCenter - 219658).Prime := by
  rw [fullRecordGapTerm02698_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02698, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02698_fast_pow_mod_ne_one

def fullRecordGapValue02699 : Nat := fullRecordGapCenterValue - 219508

theorem fullRecordGapTerm02699_eq_value :
    recordGapCenter - 219508 = fullRecordGapValue02699 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02699_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02699 (fullRecordGapValue02699 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02699_not_prime : ¬(recordGapCenter - 219508).Prime := by
  rw [fullRecordGapTerm02699_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02699, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02699_fast_pow_mod_ne_one

def fullRecordGapValue02700 : Nat := fullRecordGapCenterValue - 219238

theorem fullRecordGapTerm02700_eq_value :
    recordGapCenter - 219238 = fullRecordGapValue02700 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02700_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02700 (fullRecordGapValue02700 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02700_not_prime : ¬(recordGapCenter - 219238).Prime := by
  rw [fullRecordGapTerm02700_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02700, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02700_fast_pow_mod_ne_one

def fullRecordGapValue02701 : Nat := fullRecordGapCenterValue - 219148

theorem fullRecordGapTerm02701_eq_value :
    recordGapCenter - 219148 = fullRecordGapValue02701 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02701_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02701 (fullRecordGapValue02701 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02701_not_prime : ¬(recordGapCenter - 219148).Prime := by
  rw [fullRecordGapTerm02701_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02701, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02701_fast_pow_mod_ne_one

def fullRecordGapValue02702 : Nat := fullRecordGapCenterValue - 219034

theorem fullRecordGapTerm02702_eq_value :
    recordGapCenter - 219034 = fullRecordGapValue02702 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02702_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02702 (fullRecordGapValue02702 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02702_not_prime : ¬(recordGapCenter - 219034).Prime := by
  rw [fullRecordGapTerm02702_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02702, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02702_fast_pow_mod_ne_one

def fullRecordGapValue02703 : Nat := fullRecordGapCenterValue - 219004

theorem fullRecordGapTerm02703_eq_value :
    recordGapCenter - 219004 = fullRecordGapValue02703 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02703_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02703 (fullRecordGapValue02703 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02703_not_prime : ¬(recordGapCenter - 219004).Prime := by
  rw [fullRecordGapTerm02703_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02703, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02703_fast_pow_mod_ne_one

def fullRecordGapValue02704 : Nat := fullRecordGapCenterValue - 218908

theorem fullRecordGapTerm02704_eq_value :
    recordGapCenter - 218908 = fullRecordGapValue02704 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02704_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02704 (fullRecordGapValue02704 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02704_not_prime : ¬(recordGapCenter - 218908).Prime := by
  rw [fullRecordGapTerm02704_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02704, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02704_fast_pow_mod_ne_one

def fullRecordGapValue02705 : Nat := fullRecordGapCenterValue - 218700

theorem fullRecordGapTerm02705_eq_value :
    recordGapCenter - 218700 = fullRecordGapValue02705 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02705_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02705 (fullRecordGapValue02705 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02705_not_prime : ¬(recordGapCenter - 218700).Prime := by
  rw [fullRecordGapTerm02705_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02705, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02705_fast_pow_mod_ne_one

def fullRecordGapValue02706 : Nat := fullRecordGapCenterValue - 218668

theorem fullRecordGapTerm02706_eq_value :
    recordGapCenter - 218668 = fullRecordGapValue02706 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02706_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02706 (fullRecordGapValue02706 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02706_not_prime : ¬(recordGapCenter - 218668).Prime := by
  rw [fullRecordGapTerm02706_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02706, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02706_fast_pow_mod_ne_one

def fullRecordGapValue02707 : Nat := fullRecordGapCenterValue - 218458

theorem fullRecordGapTerm02707_eq_value :
    recordGapCenter - 218458 = fullRecordGapValue02707 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02707_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02707 (fullRecordGapValue02707 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02707_not_prime : ¬(recordGapCenter - 218458).Prime := by
  rw [fullRecordGapTerm02707_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02707, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02707_fast_pow_mod_ne_one

def fullRecordGapValue02708 : Nat := fullRecordGapCenterValue - 218404

theorem fullRecordGapTerm02708_eq_value :
    recordGapCenter - 218404 = fullRecordGapValue02708 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02708_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02708 (fullRecordGapValue02708 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02708_not_prime : ¬(recordGapCenter - 218404).Prime := by
  rw [fullRecordGapTerm02708_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02708, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02708_fast_pow_mod_ne_one

def fullRecordGapValue02709 : Nat := fullRecordGapCenterValue - 218308

theorem fullRecordGapTerm02709_eq_value :
    recordGapCenter - 218308 = fullRecordGapValue02709 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02709_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02709 (fullRecordGapValue02709 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02709_not_prime : ¬(recordGapCenter - 218308).Prime := by
  rw [fullRecordGapTerm02709_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02709, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02709_fast_pow_mod_ne_one

def fullRecordGapValue02710 : Nat := fullRecordGapCenterValue - 218242

theorem fullRecordGapTerm02710_eq_value :
    recordGapCenter - 218242 = fullRecordGapValue02710 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02710_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02710 (fullRecordGapValue02710 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02710_not_prime : ¬(recordGapCenter - 218242).Prime := by
  rw [fullRecordGapTerm02710_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02710, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02710_fast_pow_mod_ne_one

def fullRecordGapValue02711 : Nat := fullRecordGapCenterValue - 218188

theorem fullRecordGapTerm02711_eq_value :
    recordGapCenter - 218188 = fullRecordGapValue02711 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02711_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02711 (fullRecordGapValue02711 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02711_not_prime : ¬(recordGapCenter - 218188).Prime := by
  rw [fullRecordGapTerm02711_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02711, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02711_fast_pow_mod_ne_one

def fullRecordGapValue02712 : Nat := fullRecordGapCenterValue - 217942

theorem fullRecordGapTerm02712_eq_value :
    recordGapCenter - 217942 = fullRecordGapValue02712 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02712_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02712 (fullRecordGapValue02712 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02712_not_prime : ¬(recordGapCenter - 217942).Prime := by
  rw [fullRecordGapTerm02712_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02712, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02712_fast_pow_mod_ne_one

def fullRecordGapValue02713 : Nat := fullRecordGapCenterValue - 217774

theorem fullRecordGapTerm02713_eq_value :
    recordGapCenter - 217774 = fullRecordGapValue02713 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02713_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02713 (fullRecordGapValue02713 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02713_not_prime : ¬(recordGapCenter - 217774).Prime := by
  rw [fullRecordGapTerm02713_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02713, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02713_fast_pow_mod_ne_one

def fullRecordGapValue02714 : Nat := fullRecordGapCenterValue - 217762

theorem fullRecordGapTerm02714_eq_value :
    recordGapCenter - 217762 = fullRecordGapValue02714 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02714_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02714 (fullRecordGapValue02714 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02714_not_prime : ¬(recordGapCenter - 217762).Prime := by
  rw [fullRecordGapTerm02714_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02714, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02714_fast_pow_mod_ne_one

def fullRecordGapValue02715 : Nat := fullRecordGapCenterValue - 217654

theorem fullRecordGapTerm02715_eq_value :
    recordGapCenter - 217654 = fullRecordGapValue02715 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02715_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02715 (fullRecordGapValue02715 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02715_not_prime : ¬(recordGapCenter - 217654).Prime := by
  rw [fullRecordGapTerm02715_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02715, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02715_fast_pow_mod_ne_one

def fullRecordGapValue02716 : Nat := fullRecordGapCenterValue - 217468

theorem fullRecordGapTerm02716_eq_value :
    recordGapCenter - 217468 = fullRecordGapValue02716 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02716_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02716 (fullRecordGapValue02716 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02716_not_prime : ¬(recordGapCenter - 217468).Prime := by
  rw [fullRecordGapTerm02716_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02716, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02716_fast_pow_mod_ne_one

def fullRecordGapValue02717 : Nat := fullRecordGapCenterValue - 217354

theorem fullRecordGapTerm02717_eq_value :
    recordGapCenter - 217354 = fullRecordGapValue02717 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02717_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02717 (fullRecordGapValue02717 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02717_not_prime : ¬(recordGapCenter - 217354).Prime := by
  rw [fullRecordGapTerm02717_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02717, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02717_fast_pow_mod_ne_one

def fullRecordGapValue02718 : Nat := fullRecordGapCenterValue - 217324

theorem fullRecordGapTerm02718_eq_value :
    recordGapCenter - 217324 = fullRecordGapValue02718 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02718_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02718 (fullRecordGapValue02718 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02718_not_prime : ¬(recordGapCenter - 217324).Prime := by
  rw [fullRecordGapTerm02718_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02718, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02718_fast_pow_mod_ne_one

def fullRecordGapValue02719 : Nat := fullRecordGapCenterValue - 217174

theorem fullRecordGapTerm02719_eq_value :
    recordGapCenter - 217174 = fullRecordGapValue02719 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02719_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02719 (fullRecordGapValue02719 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02719_not_prime : ¬(recordGapCenter - 217174).Prime := by
  rw [fullRecordGapTerm02719_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02719, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02719_fast_pow_mod_ne_one

def fullRecordGapValue02720 : Nat := fullRecordGapCenterValue - 217114

theorem fullRecordGapTerm02720_eq_value :
    recordGapCenter - 217114 = fullRecordGapValue02720 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02720_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02720 (fullRecordGapValue02720 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02720_not_prime : ¬(recordGapCenter - 217114).Prime := by
  rw [fullRecordGapTerm02720_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02720, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02720_fast_pow_mod_ne_one

def fullRecordGapValue02721 : Nat := fullRecordGapCenterValue - 217108

theorem fullRecordGapTerm02721_eq_value :
    recordGapCenter - 217108 = fullRecordGapValue02721 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02721_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02721 (fullRecordGapValue02721 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02721_not_prime : ¬(recordGapCenter - 217108).Prime := by
  rw [fullRecordGapTerm02721_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02721, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02721_fast_pow_mod_ne_one

def fullRecordGapValue02722 : Nat := fullRecordGapCenterValue - 216922

theorem fullRecordGapTerm02722_eq_value :
    recordGapCenter - 216922 = fullRecordGapValue02722 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02722_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02722 (fullRecordGapValue02722 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02722_not_prime : ¬(recordGapCenter - 216922).Prime := by
  rw [fullRecordGapTerm02722_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02722, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02722_fast_pow_mod_ne_one

def fullRecordGapValue02723 : Nat := fullRecordGapCenterValue - 216772

theorem fullRecordGapTerm02723_eq_value :
    recordGapCenter - 216772 = fullRecordGapValue02723 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02723_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02723 (fullRecordGapValue02723 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02723_not_prime : ¬(recordGapCenter - 216772).Prime := by
  rw [fullRecordGapTerm02723_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02723, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02723_fast_pow_mod_ne_one

def fullRecordGapValue02724 : Nat := fullRecordGapCenterValue - 216382

theorem fullRecordGapTerm02724_eq_value :
    recordGapCenter - 216382 = fullRecordGapValue02724 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02724_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02724 (fullRecordGapValue02724 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02724_not_prime : ¬(recordGapCenter - 216382).Prime := by
  rw [fullRecordGapTerm02724_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02724, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02724_fast_pow_mod_ne_one

def fullRecordGapValue02725 : Nat := fullRecordGapCenterValue - 216358

theorem fullRecordGapTerm02725_eq_value :
    recordGapCenter - 216358 = fullRecordGapValue02725 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02725_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02725 (fullRecordGapValue02725 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02725_not_prime : ¬(recordGapCenter - 216358).Prime := by
  rw [fullRecordGapTerm02725_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02725, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02725_fast_pow_mod_ne_one

def fullRecordGapValue02726 : Nat := fullRecordGapCenterValue - 216262

theorem fullRecordGapTerm02726_eq_value :
    recordGapCenter - 216262 = fullRecordGapValue02726 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02726_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02726 (fullRecordGapValue02726 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02726_not_prime : ¬(recordGapCenter - 216262).Prime := by
  rw [fullRecordGapTerm02726_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02726, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02726_fast_pow_mod_ne_one

def fullRecordGapValue02727 : Nat := fullRecordGapCenterValue - 216214

theorem fullRecordGapTerm02727_eq_value :
    recordGapCenter - 216214 = fullRecordGapValue02727 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02727_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02727 (fullRecordGapValue02727 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02727_not_prime : ¬(recordGapCenter - 216214).Prime := by
  rw [fullRecordGapTerm02727_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02727, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02727_fast_pow_mod_ne_one

def fullRecordGapValue02728 : Nat := fullRecordGapCenterValue - 216090

theorem fullRecordGapTerm02728_eq_value :
    recordGapCenter - 216090 = fullRecordGapValue02728 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02728_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02728 (fullRecordGapValue02728 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02728_not_prime : ¬(recordGapCenter - 216090).Prime := by
  rw [fullRecordGapTerm02728_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02728, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02728_fast_pow_mod_ne_one

def fullRecordGapValue02729 : Nat := fullRecordGapCenterValue - 216082

theorem fullRecordGapTerm02729_eq_value :
    recordGapCenter - 216082 = fullRecordGapValue02729 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02729_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02729 (fullRecordGapValue02729 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02729_not_prime : ¬(recordGapCenter - 216082).Prime := by
  rw [fullRecordGapTerm02729_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02729, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02729_fast_pow_mod_ne_one

def fullRecordGapValue02730 : Nat := fullRecordGapCenterValue - 216052

theorem fullRecordGapTerm02730_eq_value :
    recordGapCenter - 216052 = fullRecordGapValue02730 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02730_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02730 (fullRecordGapValue02730 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02730_not_prime : ¬(recordGapCenter - 216052).Prime := by
  rw [fullRecordGapTerm02730_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02730, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02730_fast_pow_mod_ne_one

def fullRecordGapValue02731 : Nat := fullRecordGapCenterValue - 216004

theorem fullRecordGapTerm02731_eq_value :
    recordGapCenter - 216004 = fullRecordGapValue02731 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02731_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02731 (fullRecordGapValue02731 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02731_not_prime : ¬(recordGapCenter - 216004).Prime := by
  rw [fullRecordGapTerm02731_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02731, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02731_fast_pow_mod_ne_one

def fullRecordGapValue02732 : Nat := fullRecordGapCenterValue - 215854

theorem fullRecordGapTerm02732_eq_value :
    recordGapCenter - 215854 = fullRecordGapValue02732 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02732_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02732 (fullRecordGapValue02732 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02732_not_prime : ¬(recordGapCenter - 215854).Prime := by
  rw [fullRecordGapTerm02732_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02732, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02732_fast_pow_mod_ne_one

def fullRecordGapValue02733 : Nat := fullRecordGapCenterValue - 215794

theorem fullRecordGapTerm02733_eq_value :
    recordGapCenter - 215794 = fullRecordGapValue02733 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02733_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02733 (fullRecordGapValue02733 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02733_not_prime : ¬(recordGapCenter - 215794).Prime := by
  rw [fullRecordGapTerm02733_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02733, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02733_fast_pow_mod_ne_one

def fullRecordGapValue02734 : Nat := fullRecordGapCenterValue - 215674

theorem fullRecordGapTerm02734_eq_value :
    recordGapCenter - 215674 = fullRecordGapValue02734 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02734_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02734 (fullRecordGapValue02734 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02734_not_prime : ¬(recordGapCenter - 215674).Prime := by
  rw [fullRecordGapTerm02734_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02734, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02734_fast_pow_mod_ne_one

def fullRecordGapValue02735 : Nat := fullRecordGapCenterValue - 215668

theorem fullRecordGapTerm02735_eq_value :
    recordGapCenter - 215668 = fullRecordGapValue02735 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02735_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02735 (fullRecordGapValue02735 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02735_not_prime : ¬(recordGapCenter - 215668).Prime := by
  rw [fullRecordGapTerm02735_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02735, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02735_fast_pow_mod_ne_one

def fullRecordGapValue02736 : Nat := fullRecordGapCenterValue - 215554

theorem fullRecordGapTerm02736_eq_value :
    recordGapCenter - 215554 = fullRecordGapValue02736 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02736_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02736 (fullRecordGapValue02736 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02736_not_prime : ¬(recordGapCenter - 215554).Prime := by
  rw [fullRecordGapTerm02736_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02736, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02736_fast_pow_mod_ne_one

def fullRecordGapValue02737 : Nat := fullRecordGapCenterValue - 215374

theorem fullRecordGapTerm02737_eq_value :
    recordGapCenter - 215374 = fullRecordGapValue02737 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02737_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02737 (fullRecordGapValue02737 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02737_not_prime : ¬(recordGapCenter - 215374).Prime := by
  rw [fullRecordGapTerm02737_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02737, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02737_fast_pow_mod_ne_one

def fullRecordGapValue02738 : Nat := fullRecordGapCenterValue - 214924

theorem fullRecordGapTerm02738_eq_value :
    recordGapCenter - 214924 = fullRecordGapValue02738 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02738_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02738 (fullRecordGapValue02738 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02738_not_prime : ¬(recordGapCenter - 214924).Prime := by
  rw [fullRecordGapTerm02738_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02738, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02738_fast_pow_mod_ne_one

def fullRecordGapValue02739 : Nat := fullRecordGapCenterValue - 214678

theorem fullRecordGapTerm02739_eq_value :
    recordGapCenter - 214678 = fullRecordGapValue02739 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02739_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02739 (fullRecordGapValue02739 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02739_not_prime : ¬(recordGapCenter - 214678).Prime := by
  rw [fullRecordGapTerm02739_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02739, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02739_fast_pow_mod_ne_one

def fullRecordGapValue02740 : Nat := fullRecordGapCenterValue - 214612

theorem fullRecordGapTerm02740_eq_value :
    recordGapCenter - 214612 = fullRecordGapValue02740 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02740_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02740 (fullRecordGapValue02740 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02740_not_prime : ¬(recordGapCenter - 214612).Prime := by
  rw [fullRecordGapTerm02740_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02740, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02740_fast_pow_mod_ne_one

def fullRecordGapValue02741 : Nat := fullRecordGapCenterValue - 214492

theorem fullRecordGapTerm02741_eq_value :
    recordGapCenter - 214492 = fullRecordGapValue02741 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02741_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02741 (fullRecordGapValue02741 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02741_not_prime : ¬(recordGapCenter - 214492).Prime := by
  rw [fullRecordGapTerm02741_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02741, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02741_fast_pow_mod_ne_one

def fullRecordGapValue02742 : Nat := fullRecordGapCenterValue - 214342

theorem fullRecordGapTerm02742_eq_value :
    recordGapCenter - 214342 = fullRecordGapValue02742 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02742_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02742 (fullRecordGapValue02742 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02742_not_prime : ¬(recordGapCenter - 214342).Prime := by
  rw [fullRecordGapTerm02742_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02742, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02742_fast_pow_mod_ne_one

def fullRecordGapValue02743 : Nat := fullRecordGapCenterValue - 214114

theorem fullRecordGapTerm02743_eq_value :
    recordGapCenter - 214114 = fullRecordGapValue02743 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02743_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02743 (fullRecordGapValue02743 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02743_not_prime : ¬(recordGapCenter - 214114).Prime := by
  rw [fullRecordGapTerm02743_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02743, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02743_fast_pow_mod_ne_one

def fullRecordGapValue02744 : Nat := fullRecordGapCenterValue - 213814

theorem fullRecordGapTerm02744_eq_value :
    recordGapCenter - 213814 = fullRecordGapValue02744 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02744_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02744 (fullRecordGapValue02744 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02744_not_prime : ¬(recordGapCenter - 213814).Prime := by
  rw [fullRecordGapTerm02744_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02744, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02744_fast_pow_mod_ne_one

def fullRecordGapValue02745 : Nat := fullRecordGapCenterValue - 213748

theorem fullRecordGapTerm02745_eq_value :
    recordGapCenter - 213748 = fullRecordGapValue02745 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02745_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02745 (fullRecordGapValue02745 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02745_not_prime : ¬(recordGapCenter - 213748).Prime := by
  rw [fullRecordGapTerm02745_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02745, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02745_fast_pow_mod_ne_one

def fullRecordGapValue02746 : Nat := fullRecordGapCenterValue - 213628

theorem fullRecordGapTerm02746_eq_value :
    recordGapCenter - 213628 = fullRecordGapValue02746 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02746_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02746 (fullRecordGapValue02746 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02746_not_prime : ¬(recordGapCenter - 213628).Prime := by
  rw [fullRecordGapTerm02746_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02746, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02746_fast_pow_mod_ne_one

def fullRecordGapValue02747 : Nat := fullRecordGapCenterValue - 213574

theorem fullRecordGapTerm02747_eq_value :
    recordGapCenter - 213574 = fullRecordGapValue02747 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02747_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02747 (fullRecordGapValue02747 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02747_not_prime : ¬(recordGapCenter - 213574).Prime := by
  rw [fullRecordGapTerm02747_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02747, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02747_fast_pow_mod_ne_one

def fullRecordGapValue02748 : Nat := fullRecordGapCenterValue - 213562

theorem fullRecordGapTerm02748_eq_value :
    recordGapCenter - 213562 = fullRecordGapValue02748 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02748_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02748 (fullRecordGapValue02748 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02748_not_prime : ¬(recordGapCenter - 213562).Prime := by
  rw [fullRecordGapTerm02748_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02748, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02748_fast_pow_mod_ne_one

def fullRecordGapValue02749 : Nat := fullRecordGapCenterValue - 213444

theorem fullRecordGapTerm02749_eq_value :
    recordGapCenter - 213444 = fullRecordGapValue02749 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02749_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02749 (fullRecordGapValue02749 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02749_not_prime : ¬(recordGapCenter - 213444).Prime := by
  rw [fullRecordGapTerm02749_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02749, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02749_fast_pow_mod_ne_one

def fullRecordGapValue02750 : Nat := fullRecordGapCenterValue - 213442

theorem fullRecordGapTerm02750_eq_value :
    recordGapCenter - 213442 = fullRecordGapValue02750 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02750_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02750 (fullRecordGapValue02750 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02750_not_prime : ¬(recordGapCenter - 213442).Prime := by
  rw [fullRecordGapTerm02750_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02750, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02750_fast_pow_mod_ne_one

def fullRecordGapValue02751 : Nat := fullRecordGapCenterValue - 213412

theorem fullRecordGapTerm02751_eq_value :
    recordGapCenter - 213412 = fullRecordGapValue02751 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02751_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02751 (fullRecordGapValue02751 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02751_not_prime : ¬(recordGapCenter - 213412).Prime := by
  rw [fullRecordGapTerm02751_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02751, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02751_fast_pow_mod_ne_one

def fullRecordGapValue02752 : Nat := fullRecordGapCenterValue - 213292

theorem fullRecordGapTerm02752_eq_value :
    recordGapCenter - 213292 = fullRecordGapValue02752 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02752_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02752 (fullRecordGapValue02752 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02752_not_prime : ¬(recordGapCenter - 213292).Prime := by
  rw [fullRecordGapTerm02752_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02752, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02752_fast_pow_mod_ne_one

def fullRecordGapValue02753 : Nat := fullRecordGapCenterValue - 213274

theorem fullRecordGapTerm02753_eq_value :
    recordGapCenter - 213274 = fullRecordGapValue02753 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02753_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02753 (fullRecordGapValue02753 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02753_not_prime : ¬(recordGapCenter - 213274).Prime := by
  rw [fullRecordGapTerm02753_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02753, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02753_fast_pow_mod_ne_one

def fullRecordGapValue02754 : Nat := fullRecordGapCenterValue - 213082

theorem fullRecordGapTerm02754_eq_value :
    recordGapCenter - 213082 = fullRecordGapValue02754 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02754_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02754 (fullRecordGapValue02754 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02754_not_prime : ¬(recordGapCenter - 213082).Prime := by
  rw [fullRecordGapTerm02754_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02754, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02754_fast_pow_mod_ne_one

def fullRecordGapValue02755 : Nat := fullRecordGapCenterValue - 212974

theorem fullRecordGapTerm02755_eq_value :
    recordGapCenter - 212974 = fullRecordGapValue02755 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02755_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02755 (fullRecordGapValue02755 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02755_not_prime : ¬(recordGapCenter - 212974).Prime := by
  rw [fullRecordGapTerm02755_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02755, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02755_fast_pow_mod_ne_one

def fullRecordGapValue02756 : Nat := fullRecordGapCenterValue - 212782

theorem fullRecordGapTerm02756_eq_value :
    recordGapCenter - 212782 = fullRecordGapValue02756 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02756_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02756 (fullRecordGapValue02756 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02756_not_prime : ¬(recordGapCenter - 212782).Prime := by
  rw [fullRecordGapTerm02756_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02756, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02756_fast_pow_mod_ne_one

def fullRecordGapValue02757 : Nat := fullRecordGapCenterValue - 212698

theorem fullRecordGapTerm02757_eq_value :
    recordGapCenter - 212698 = fullRecordGapValue02757 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02757_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02757 (fullRecordGapValue02757 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02757_not_prime : ¬(recordGapCenter - 212698).Prime := by
  rw [fullRecordGapTerm02757_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02757, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02757_fast_pow_mod_ne_one

def fullRecordGapValue02758 : Nat := fullRecordGapCenterValue - 212662

theorem fullRecordGapTerm02758_eq_value :
    recordGapCenter - 212662 = fullRecordGapValue02758 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02758_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02758 (fullRecordGapValue02758 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02758_not_prime : ¬(recordGapCenter - 212662).Prime := by
  rw [fullRecordGapTerm02758_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02758, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02758_fast_pow_mod_ne_one

def fullRecordGapValue02759 : Nat := fullRecordGapCenterValue - 212434

theorem fullRecordGapTerm02759_eq_value :
    recordGapCenter - 212434 = fullRecordGapValue02759 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02759_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02759 (fullRecordGapValue02759 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02759_not_prime : ¬(recordGapCenter - 212434).Prime := by
  rw [fullRecordGapTerm02759_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02759, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02759_fast_pow_mod_ne_one

def fullRecordGapValue02760 : Nat := fullRecordGapCenterValue - 212404

theorem fullRecordGapTerm02760_eq_value :
    recordGapCenter - 212404 = fullRecordGapValue02760 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02760_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02760 (fullRecordGapValue02760 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02760_not_prime : ¬(recordGapCenter - 212404).Prime := by
  rw [fullRecordGapTerm02760_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02760, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02760_fast_pow_mod_ne_one

def fullRecordGapValue02761 : Nat := fullRecordGapCenterValue - 212242

theorem fullRecordGapTerm02761_eq_value :
    recordGapCenter - 212242 = fullRecordGapValue02761 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02761_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02761 (fullRecordGapValue02761 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02761_not_prime : ¬(recordGapCenter - 212242).Prime := by
  rw [fullRecordGapTerm02761_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02761, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02761_fast_pow_mod_ne_one

def fullRecordGapValue02762 : Nat := fullRecordGapCenterValue - 212218

theorem fullRecordGapTerm02762_eq_value :
    recordGapCenter - 212218 = fullRecordGapValue02762 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02762_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02762 (fullRecordGapValue02762 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02762_not_prime : ¬(recordGapCenter - 212218).Prime := by
  rw [fullRecordGapTerm02762_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02762, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02762_fast_pow_mod_ne_one

def fullRecordGapValue02763 : Nat := fullRecordGapCenterValue - 211942

theorem fullRecordGapTerm02763_eq_value :
    recordGapCenter - 211942 = fullRecordGapValue02763 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02763_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02763 (fullRecordGapValue02763 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02763_not_prime : ¬(recordGapCenter - 211942).Prime := by
  rw [fullRecordGapTerm02763_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02763, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02763_fast_pow_mod_ne_one

def fullRecordGapValue02764 : Nat := fullRecordGapCenterValue - 211852

theorem fullRecordGapTerm02764_eq_value :
    recordGapCenter - 211852 = fullRecordGapValue02764 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02764_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02764 (fullRecordGapValue02764 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02764_not_prime : ¬(recordGapCenter - 211852).Prime := by
  rw [fullRecordGapTerm02764_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02764, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02764_fast_pow_mod_ne_one

def fullRecordGapValue02765 : Nat := fullRecordGapCenterValue - 211804

theorem fullRecordGapTerm02765_eq_value :
    recordGapCenter - 211804 = fullRecordGapValue02765 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02765_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02765 (fullRecordGapValue02765 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02765_not_prime : ¬(recordGapCenter - 211804).Prime := by
  rw [fullRecordGapTerm02765_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02765, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02765_fast_pow_mod_ne_one

def fullRecordGapValue02766 : Nat := fullRecordGapCenterValue - 211750

theorem fullRecordGapTerm02766_eq_value :
    recordGapCenter - 211750 = fullRecordGapValue02766 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02766_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02766 (fullRecordGapValue02766 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02766_not_prime : ¬(recordGapCenter - 211750).Prime := by
  rw [fullRecordGapTerm02766_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02766, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02766_fast_pow_mod_ne_one

def fullRecordGapValue02767 : Nat := fullRecordGapCenterValue - 211680

theorem fullRecordGapTerm02767_eq_value :
    recordGapCenter - 211680 = fullRecordGapValue02767 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02767_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02767 (fullRecordGapValue02767 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02767_not_prime : ¬(recordGapCenter - 211680).Prime := by
  rw [fullRecordGapTerm02767_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02767, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02767_fast_pow_mod_ne_one

def fullRecordGapValue02768 : Nat := fullRecordGapCenterValue - 211612

theorem fullRecordGapTerm02768_eq_value :
    recordGapCenter - 211612 = fullRecordGapValue02768 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02768_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02768 (fullRecordGapValue02768 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02768_not_prime : ¬(recordGapCenter - 211612).Prime := by
  rw [fullRecordGapTerm02768_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02768, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02768_fast_pow_mod_ne_one

def fullRecordGapValue02769 : Nat := fullRecordGapCenterValue - 211348

theorem fullRecordGapTerm02769_eq_value :
    recordGapCenter - 211348 = fullRecordGapValue02769 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02769_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02769 (fullRecordGapValue02769 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02769_not_prime : ¬(recordGapCenter - 211348).Prime := by
  rw [fullRecordGapTerm02769_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02769, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02769_fast_pow_mod_ne_one

def fullRecordGapValue02770 : Nat := fullRecordGapCenterValue - 211054

theorem fullRecordGapTerm02770_eq_value :
    recordGapCenter - 211054 = fullRecordGapValue02770 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02770_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02770 (fullRecordGapValue02770 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02770_not_prime : ¬(recordGapCenter - 211054).Prime := by
  rw [fullRecordGapTerm02770_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02770, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02770_fast_pow_mod_ne_one

def fullRecordGapValue02771 : Nat := fullRecordGapCenterValue - 210814

theorem fullRecordGapTerm02771_eq_value :
    recordGapCenter - 210814 = fullRecordGapValue02771 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02771_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02771 (fullRecordGapValue02771 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02771_not_prime : ¬(recordGapCenter - 210814).Prime := by
  rw [fullRecordGapTerm02771_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02771, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02771_fast_pow_mod_ne_one

def fullRecordGapValue02772 : Nat := fullRecordGapCenterValue - 210802

theorem fullRecordGapTerm02772_eq_value :
    recordGapCenter - 210802 = fullRecordGapValue02772 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02772_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02772 (fullRecordGapValue02772 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02772_not_prime : ¬(recordGapCenter - 210802).Prime := by
  rw [fullRecordGapTerm02772_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02772, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02772_fast_pow_mod_ne_one

def fullRecordGapValue02773 : Nat := fullRecordGapCenterValue - 210718

theorem fullRecordGapTerm02773_eq_value :
    recordGapCenter - 210718 = fullRecordGapValue02773 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02773_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02773 (fullRecordGapValue02773 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02773_not_prime : ¬(recordGapCenter - 210718).Prime := by
  rw [fullRecordGapTerm02773_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02773, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02773_fast_pow_mod_ne_one

def fullRecordGapValue02774 : Nat := fullRecordGapCenterValue - 210682

theorem fullRecordGapTerm02774_eq_value :
    recordGapCenter - 210682 = fullRecordGapValue02774 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02774_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02774 (fullRecordGapValue02774 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02774_not_prime : ¬(recordGapCenter - 210682).Prime := by
  rw [fullRecordGapTerm02774_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02774, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02774_fast_pow_mod_ne_one

def fullRecordGapValue02775 : Nat := fullRecordGapCenterValue - 210502

theorem fullRecordGapTerm02775_eq_value :
    recordGapCenter - 210502 = fullRecordGapValue02775 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02775_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02775 (fullRecordGapValue02775 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02775_not_prime : ¬(recordGapCenter - 210502).Prime := by
  rw [fullRecordGapTerm02775_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02775, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02775_fast_pow_mod_ne_one

def fullRecordGapValue02776 : Nat := fullRecordGapCenterValue - 210244

theorem fullRecordGapTerm02776_eq_value :
    recordGapCenter - 210244 = fullRecordGapValue02776 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02776_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02776 (fullRecordGapValue02776 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02776_not_prime : ¬(recordGapCenter - 210244).Prime := by
  rw [fullRecordGapTerm02776_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02776, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02776_fast_pow_mod_ne_one

def fullRecordGapValue02777 : Nat := fullRecordGapCenterValue - 210142

theorem fullRecordGapTerm02777_eq_value :
    recordGapCenter - 210142 = fullRecordGapValue02777 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02777_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02777 (fullRecordGapValue02777 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02777_not_prime : ¬(recordGapCenter - 210142).Prime := by
  rw [fullRecordGapTerm02777_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02777, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02777_fast_pow_mod_ne_one

def fullRecordGapValue02778 : Nat := fullRecordGapCenterValue - 210004

theorem fullRecordGapTerm02778_eq_value :
    recordGapCenter - 210004 = fullRecordGapValue02778 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02778_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02778 (fullRecordGapValue02778 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02778_not_prime : ¬(recordGapCenter - 210004).Prime := by
  rw [fullRecordGapTerm02778_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02778, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02778_fast_pow_mod_ne_one

def fullRecordGapValue02779 : Nat := fullRecordGapCenterValue - 209758

theorem fullRecordGapTerm02779_eq_value :
    recordGapCenter - 209758 = fullRecordGapValue02779 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02779_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02779 (fullRecordGapValue02779 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02779_not_prime : ¬(recordGapCenter - 209758).Prime := by
  rw [fullRecordGapTerm02779_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02779, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02779_fast_pow_mod_ne_one

def fullRecordGapValue02780 : Nat := fullRecordGapCenterValue - 209548

theorem fullRecordGapTerm02780_eq_value :
    recordGapCenter - 209548 = fullRecordGapValue02780 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02780_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02780 (fullRecordGapValue02780 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02780_not_prime : ¬(recordGapCenter - 209548).Prime := by
  rw [fullRecordGapTerm02780_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02780, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02780_fast_pow_mod_ne_one

def fullRecordGapValue02781 : Nat := fullRecordGapCenterValue - 209452

theorem fullRecordGapTerm02781_eq_value :
    recordGapCenter - 209452 = fullRecordGapValue02781 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02781_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02781 (fullRecordGapValue02781 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02781_not_prime : ¬(recordGapCenter - 209452).Prime := by
  rw [fullRecordGapTerm02781_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02781, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02781_fast_pow_mod_ne_one

def fullRecordGapValue02782 : Nat := fullRecordGapCenterValue - 209122

theorem fullRecordGapTerm02782_eq_value :
    recordGapCenter - 209122 = fullRecordGapValue02782 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02782_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02782 (fullRecordGapValue02782 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02782_not_prime : ¬(recordGapCenter - 209122).Prime := by
  rw [fullRecordGapTerm02782_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02782, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02782_fast_pow_mod_ne_one

def fullRecordGapValue02783 : Nat := fullRecordGapCenterValue - 209088

theorem fullRecordGapTerm02783_eq_value :
    recordGapCenter - 209088 = fullRecordGapValue02783 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02783_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02783 (fullRecordGapValue02783 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02783_not_prime : ¬(recordGapCenter - 209088).Prime := by
  rw [fullRecordGapTerm02783_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02783, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02783_fast_pow_mod_ne_one

def fullRecordGapValue02784 : Nat := fullRecordGapCenterValue - 208918

theorem fullRecordGapTerm02784_eq_value :
    recordGapCenter - 208918 = fullRecordGapValue02784 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02784_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02784 (fullRecordGapValue02784 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02784_not_prime : ¬(recordGapCenter - 208918).Prime := by
  rw [fullRecordGapTerm02784_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02784, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02784_fast_pow_mod_ne_one

def fullRecordGapValue02785 : Nat := fullRecordGapCenterValue - 208834

theorem fullRecordGapTerm02785_eq_value :
    recordGapCenter - 208834 = fullRecordGapValue02785 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02785_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02785 (fullRecordGapValue02785 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02785_not_prime : ¬(recordGapCenter - 208834).Prime := by
  rw [fullRecordGapTerm02785_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02785, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02785_fast_pow_mod_ne_one

def fullRecordGapValue02786 : Nat := fullRecordGapCenterValue - 208738

theorem fullRecordGapTerm02786_eq_value :
    recordGapCenter - 208738 = fullRecordGapValue02786 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02786_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02786 (fullRecordGapValue02786 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02786_not_prime : ¬(recordGapCenter - 208738).Prime := by
  rw [fullRecordGapTerm02786_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02786, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02786_fast_pow_mod_ne_one

def fullRecordGapValue02787 : Nat := fullRecordGapCenterValue - 208708

theorem fullRecordGapTerm02787_eq_value :
    recordGapCenter - 208708 = fullRecordGapValue02787 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02787_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02787 (fullRecordGapValue02787 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02787_not_prime : ¬(recordGapCenter - 208708).Prime := by
  rw [fullRecordGapTerm02787_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02787, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02787_fast_pow_mod_ne_one

def fullRecordGapValue02788 : Nat := fullRecordGapCenterValue - 208612

theorem fullRecordGapTerm02788_eq_value :
    recordGapCenter - 208612 = fullRecordGapValue02788 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02788_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02788 (fullRecordGapValue02788 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02788_not_prime : ¬(recordGapCenter - 208612).Prime := by
  rw [fullRecordGapTerm02788_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02788, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02788_fast_pow_mod_ne_one

def fullRecordGapValue02789 : Nat := fullRecordGapCenterValue - 208414

theorem fullRecordGapTerm02789_eq_value :
    recordGapCenter - 208414 = fullRecordGapValue02789 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02789_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02789 (fullRecordGapValue02789 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02789_not_prime : ¬(recordGapCenter - 208414).Prime := by
  rw [fullRecordGapTerm02789_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02789, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02789_fast_pow_mod_ne_one

def fullRecordGapValue02790 : Nat := fullRecordGapCenterValue - 208324

theorem fullRecordGapTerm02790_eq_value :
    recordGapCenter - 208324 = fullRecordGapValue02790 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02790_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02790 (fullRecordGapValue02790 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02790_not_prime : ¬(recordGapCenter - 208324).Prime := by
  rw [fullRecordGapTerm02790_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02790, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02790_fast_pow_mod_ne_one

def fullRecordGapValue02791 : Nat := fullRecordGapCenterValue - 208228

theorem fullRecordGapTerm02791_eq_value :
    recordGapCenter - 208228 = fullRecordGapValue02791 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02791_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02791 (fullRecordGapValue02791 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02791_not_prime : ¬(recordGapCenter - 208228).Prime := by
  rw [fullRecordGapTerm02791_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02791, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02791_fast_pow_mod_ne_one

def fullRecordGapValue02792 : Nat := fullRecordGapCenterValue - 208204

theorem fullRecordGapTerm02792_eq_value :
    recordGapCenter - 208204 = fullRecordGapValue02792 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02792_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02792 (fullRecordGapValue02792 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02792_not_prime : ¬(recordGapCenter - 208204).Prime := by
  rw [fullRecordGapTerm02792_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02792, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02792_fast_pow_mod_ne_one

def fullRecordGapValue02793 : Nat := fullRecordGapCenterValue - 208084

theorem fullRecordGapTerm02793_eq_value :
    recordGapCenter - 208084 = fullRecordGapValue02793 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02793_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02793 (fullRecordGapValue02793 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02793_not_prime : ¬(recordGapCenter - 208084).Prime := by
  rw [fullRecordGapTerm02793_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02793, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02793_fast_pow_mod_ne_one

def fullRecordGapValue02794 : Nat := fullRecordGapCenterValue - 208018

theorem fullRecordGapTerm02794_eq_value :
    recordGapCenter - 208018 = fullRecordGapValue02794 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02794_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02794 (fullRecordGapValue02794 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02794_not_prime : ¬(recordGapCenter - 208018).Prime := by
  rw [fullRecordGapTerm02794_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02794, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02794_fast_pow_mod_ne_one

def fullRecordGapValue02795 : Nat := fullRecordGapCenterValue - 207982

theorem fullRecordGapTerm02795_eq_value :
    recordGapCenter - 207982 = fullRecordGapValue02795 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02795_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02795 (fullRecordGapValue02795 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02795_not_prime : ¬(recordGapCenter - 207982).Prime := by
  rw [fullRecordGapTerm02795_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02795, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02795_fast_pow_mod_ne_one

def fullRecordGapValue02796 : Nat := fullRecordGapCenterValue - 207934

theorem fullRecordGapTerm02796_eq_value :
    recordGapCenter - 207934 = fullRecordGapValue02796 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02796_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02796 (fullRecordGapValue02796 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02796_not_prime : ¬(recordGapCenter - 207934).Prime := by
  rw [fullRecordGapTerm02796_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02796, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02796_fast_pow_mod_ne_one

def fullRecordGapValue02797 : Nat := fullRecordGapCenterValue - 207900

theorem fullRecordGapTerm02797_eq_value :
    recordGapCenter - 207900 = fullRecordGapValue02797 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02797_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02797 (fullRecordGapValue02797 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02797_not_prime : ¬(recordGapCenter - 207900).Prime := by
  rw [fullRecordGapTerm02797_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02797, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02797_fast_pow_mod_ne_one

def fullRecordGapValue02798 : Nat := fullRecordGapCenterValue - 207682

theorem fullRecordGapTerm02798_eq_value :
    recordGapCenter - 207682 = fullRecordGapValue02798 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02798_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02798 (fullRecordGapValue02798 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02798_not_prime : ¬(recordGapCenter - 207682).Prime := by
  rw [fullRecordGapTerm02798_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02798, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02798_fast_pow_mod_ne_one

def fullRecordGapValue02799 : Nat := fullRecordGapCenterValue - 207652

theorem fullRecordGapTerm02799_eq_value :
    recordGapCenter - 207652 = fullRecordGapValue02799 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02799_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02799 (fullRecordGapValue02799 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02799_not_prime : ¬(recordGapCenter - 207652).Prime := by
  rw [fullRecordGapTerm02799_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02799, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02799_fast_pow_mod_ne_one

def fullRecordGapValue02800 : Nat := fullRecordGapCenterValue - 207412

theorem fullRecordGapTerm02800_eq_value :
    recordGapCenter - 207412 = fullRecordGapValue02800 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02800_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02800 (fullRecordGapValue02800 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02800_not_prime : ¬(recordGapCenter - 207412).Prime := by
  rw [fullRecordGapTerm02800_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02800, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02800_fast_pow_mod_ne_one

def fullRecordGapValue02801 : Nat := fullRecordGapCenterValue - 207268

theorem fullRecordGapTerm02801_eq_value :
    recordGapCenter - 207268 = fullRecordGapValue02801 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02801_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02801 (fullRecordGapValue02801 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02801_not_prime : ¬(recordGapCenter - 207268).Prime := by
  rw [fullRecordGapTerm02801_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02801, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02801_fast_pow_mod_ne_one

def fullRecordGapValue02802 : Nat := fullRecordGapCenterValue - 207238

theorem fullRecordGapTerm02802_eq_value :
    recordGapCenter - 207238 = fullRecordGapValue02802 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02802_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02802 (fullRecordGapValue02802 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02802_not_prime : ¬(recordGapCenter - 207238).Prime := by
  rw [fullRecordGapTerm02802_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02802, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02802_fast_pow_mod_ne_one

def fullRecordGapValue02803 : Nat := fullRecordGapCenterValue - 207058

theorem fullRecordGapTerm02803_eq_value :
    recordGapCenter - 207058 = fullRecordGapValue02803 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02803_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02803 (fullRecordGapValue02803 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02803_not_prime : ¬(recordGapCenter - 207058).Prime := by
  rw [fullRecordGapTerm02803_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02803, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02803_fast_pow_mod_ne_one

def fullRecordGapValue02804 : Nat := fullRecordGapCenterValue - 206902

theorem fullRecordGapTerm02804_eq_value :
    recordGapCenter - 206902 = fullRecordGapValue02804 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02804_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02804 (fullRecordGapValue02804 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02804_not_prime : ¬(recordGapCenter - 206902).Prime := by
  rw [fullRecordGapTerm02804_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02804, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02804_fast_pow_mod_ne_one

def fullRecordGapValue02805 : Nat := fullRecordGapCenterValue - 206842

theorem fullRecordGapTerm02805_eq_value :
    recordGapCenter - 206842 = fullRecordGapValue02805 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02805_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02805 (fullRecordGapValue02805 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02805_not_prime : ¬(recordGapCenter - 206842).Prime := by
  rw [fullRecordGapTerm02805_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02805, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02805_fast_pow_mod_ne_one

def fullRecordGapValue02806 : Nat := fullRecordGapCenterValue - 206818

theorem fullRecordGapTerm02806_eq_value :
    recordGapCenter - 206818 = fullRecordGapValue02806 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02806_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02806 (fullRecordGapValue02806 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02806_not_prime : ¬(recordGapCenter - 206818).Prime := by
  rw [fullRecordGapTerm02806_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02806, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02806_fast_pow_mod_ne_one

def fullRecordGapValue02807 : Nat := fullRecordGapCenterValue - 206698

theorem fullRecordGapTerm02807_eq_value :
    recordGapCenter - 206698 = fullRecordGapValue02807 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02807_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02807 (fullRecordGapValue02807 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02807_not_prime : ¬(recordGapCenter - 206698).Prime := by
  rw [fullRecordGapTerm02807_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02807, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02807_fast_pow_mod_ne_one

def fullRecordGapValue02808 : Nat := fullRecordGapCenterValue - 206638

theorem fullRecordGapTerm02808_eq_value :
    recordGapCenter - 206638 = fullRecordGapValue02808 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02808_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02808 (fullRecordGapValue02808 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02808_not_prime : ¬(recordGapCenter - 206638).Prime := by
  rw [fullRecordGapTerm02808_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02808, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02808_fast_pow_mod_ne_one

def fullRecordGapValue02809 : Nat := fullRecordGapCenterValue - 206614

theorem fullRecordGapTerm02809_eq_value :
    recordGapCenter - 206614 = fullRecordGapValue02809 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02809_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02809 (fullRecordGapValue02809 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02809_not_prime : ¬(recordGapCenter - 206614).Prime := by
  rw [fullRecordGapTerm02809_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02809, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02809_fast_pow_mod_ne_one

def fullRecordGapValue02810 : Nat := fullRecordGapCenterValue - 206308

theorem fullRecordGapTerm02810_eq_value :
    recordGapCenter - 206308 = fullRecordGapValue02810 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02810_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02810 (fullRecordGapValue02810 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02810_not_prime : ¬(recordGapCenter - 206308).Prime := by
  rw [fullRecordGapTerm02810_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02810, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02810_fast_pow_mod_ne_one

def fullRecordGapValue02811 : Nat := fullRecordGapCenterValue - 206250

theorem fullRecordGapTerm02811_eq_value :
    recordGapCenter - 206250 = fullRecordGapValue02811 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02811_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02811 (fullRecordGapValue02811 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02811_not_prime : ¬(recordGapCenter - 206250).Prime := by
  rw [fullRecordGapTerm02811_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02811, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02811_fast_pow_mod_ne_one

def fullRecordGapValue02812 : Nat := fullRecordGapCenterValue - 206098

theorem fullRecordGapTerm02812_eq_value :
    recordGapCenter - 206098 = fullRecordGapValue02812 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02812_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02812 (fullRecordGapValue02812 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02812_not_prime : ¬(recordGapCenter - 206098).Prime := by
  rw [fullRecordGapTerm02812_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02812, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02812_fast_pow_mod_ne_one

def fullRecordGapValue02813 : Nat := fullRecordGapCenterValue - 206068

theorem fullRecordGapTerm02813_eq_value :
    recordGapCenter - 206068 = fullRecordGapValue02813 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02813_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02813 (fullRecordGapValue02813 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02813_not_prime : ¬(recordGapCenter - 206068).Prime := by
  rw [fullRecordGapTerm02813_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02813, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02813_fast_pow_mod_ne_one

def fullRecordGapValue02814 : Nat := fullRecordGapCenterValue - 206014

theorem fullRecordGapTerm02814_eq_value :
    recordGapCenter - 206014 = fullRecordGapValue02814 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02814_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02814 (fullRecordGapValue02814 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02814_not_prime : ¬(recordGapCenter - 206014).Prime := by
  rw [fullRecordGapTerm02814_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02814, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02814_fast_pow_mod_ne_one

def fullRecordGapValue02815 : Nat := fullRecordGapCenterValue - 205522

theorem fullRecordGapTerm02815_eq_value :
    recordGapCenter - 205522 = fullRecordGapValue02815 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02815_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02815 (fullRecordGapValue02815 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02815_not_prime : ¬(recordGapCenter - 205522).Prime := by
  rw [fullRecordGapTerm02815_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02815, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02815_fast_pow_mod_ne_one

def fullRecordGapValue02816 : Nat := fullRecordGapCenterValue - 205228

theorem fullRecordGapTerm02816_eq_value :
    recordGapCenter - 205228 = fullRecordGapValue02816 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral02816_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue02816 (fullRecordGapValue02816 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm02816_not_prime : ¬(recordGapCenter - 205228).Prime := by
  rw [fullRecordGapTerm02816_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue02816, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral02816_fast_pow_mod_ne_one

end PrimeFactorUnimodality
