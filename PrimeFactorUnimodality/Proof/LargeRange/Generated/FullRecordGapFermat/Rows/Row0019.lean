import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue04609 : Nat := fullRecordGapCenterValue + 179468

theorem fullRecordGapTerm04609_eq_value :
    recordGapCenter + 179468 = fullRecordGapValue04609 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04609_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04609 (fullRecordGapValue04609 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04609_not_prime : ¬(recordGapCenter + 179468).Prime := by
  rw [fullRecordGapTerm04609_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04609, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04609_fast_pow_mod_ne_one

def fullRecordGapValue04610 : Nat := fullRecordGapCenterValue + 179618

theorem fullRecordGapTerm04610_eq_value :
    recordGapCenter + 179618 = fullRecordGapValue04610 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04610_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04610 (fullRecordGapValue04610 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04610_not_prime : ¬(recordGapCenter + 179618).Prime := by
  rw [fullRecordGapTerm04610_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04610, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04610_fast_pow_mod_ne_one

def fullRecordGapValue04611 : Nat := fullRecordGapCenterValue + 179708

theorem fullRecordGapTerm04611_eq_value :
    recordGapCenter + 179708 = fullRecordGapValue04611 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04611_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04611 (fullRecordGapValue04611 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04611_not_prime : ¬(recordGapCenter + 179708).Prime := by
  rw [fullRecordGapTerm04611_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04611, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04611_fast_pow_mod_ne_one

def fullRecordGapValue04612 : Nat := fullRecordGapCenterValue + 179756

theorem fullRecordGapTerm04612_eq_value :
    recordGapCenter + 179756 = fullRecordGapValue04612 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04612_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04612 (fullRecordGapValue04612 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04612_not_prime : ¬(recordGapCenter + 179756).Prime := by
  rw [fullRecordGapTerm04612_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04612, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04612_fast_pow_mod_ne_one

def fullRecordGapValue04613 : Nat := fullRecordGapCenterValue + 179798

theorem fullRecordGapTerm04613_eq_value :
    recordGapCenter + 179798 = fullRecordGapValue04613 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04613_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04613 (fullRecordGapValue04613 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04613_not_prime : ¬(recordGapCenter + 179798).Prime := by
  rw [fullRecordGapTerm04613_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04613, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04613_fast_pow_mod_ne_one

def fullRecordGapValue04614 : Nat := fullRecordGapCenterValue + 179852

theorem fullRecordGapTerm04614_eq_value :
    recordGapCenter + 179852 = fullRecordGapValue04614 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04614_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04614 (fullRecordGapValue04614 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04614_not_prime : ¬(recordGapCenter + 179852).Prime := by
  rw [fullRecordGapTerm04614_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04614, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04614_fast_pow_mod_ne_one

def fullRecordGapValue04615 : Nat := fullRecordGapCenterValue + 179918

theorem fullRecordGapTerm04615_eq_value :
    recordGapCenter + 179918 = fullRecordGapValue04615 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04615_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04615 (fullRecordGapValue04615 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04615_not_prime : ¬(recordGapCenter + 179918).Prime := by
  rw [fullRecordGapTerm04615_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04615, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04615_fast_pow_mod_ne_one

def fullRecordGapValue04616 : Nat := fullRecordGapCenterValue + 180002

theorem fullRecordGapTerm04616_eq_value :
    recordGapCenter + 180002 = fullRecordGapValue04616 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04616_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04616 (fullRecordGapValue04616 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04616_not_prime : ¬(recordGapCenter + 180002).Prime := by
  rw [fullRecordGapTerm04616_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04616, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04616_fast_pow_mod_ne_one

def fullRecordGapValue04617 : Nat := fullRecordGapCenterValue + 180146

theorem fullRecordGapTerm04617_eq_value :
    recordGapCenter + 180146 = fullRecordGapValue04617 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04617_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04617 (fullRecordGapValue04617 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04617_not_prime : ¬(recordGapCenter + 180146).Prime := by
  rw [fullRecordGapTerm04617_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04617, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04617_fast_pow_mod_ne_one

def fullRecordGapValue04618 : Nat := fullRecordGapCenterValue + 180542

theorem fullRecordGapTerm04618_eq_value :
    recordGapCenter + 180542 = fullRecordGapValue04618 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04618_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04618 (fullRecordGapValue04618 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04618_not_prime : ¬(recordGapCenter + 180542).Prime := by
  rw [fullRecordGapTerm04618_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04618, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04618_fast_pow_mod_ne_one

def fullRecordGapValue04619 : Nat := fullRecordGapCenterValue + 180548

theorem fullRecordGapTerm04619_eq_value :
    recordGapCenter + 180548 = fullRecordGapValue04619 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04619_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04619 (fullRecordGapValue04619 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04619_not_prime : ¬(recordGapCenter + 180548).Prime := by
  rw [fullRecordGapTerm04619_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04619, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04619_fast_pow_mod_ne_one

def fullRecordGapValue04620 : Nat := fullRecordGapCenterValue + 180716

theorem fullRecordGapTerm04620_eq_value :
    recordGapCenter + 180716 = fullRecordGapValue04620 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04620_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04620 (fullRecordGapValue04620 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04620_not_prime : ¬(recordGapCenter + 180716).Prime := by
  rw [fullRecordGapTerm04620_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04620, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04620_fast_pow_mod_ne_one

def fullRecordGapValue04621 : Nat := fullRecordGapCenterValue + 180962

theorem fullRecordGapTerm04621_eq_value :
    recordGapCenter + 180962 = fullRecordGapValue04621 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04621_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04621 (fullRecordGapValue04621 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04621_not_prime : ¬(recordGapCenter + 180962).Prime := by
  rw [fullRecordGapTerm04621_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04621, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04621_fast_pow_mod_ne_one

def fullRecordGapValue04622 : Nat := fullRecordGapCenterValue + 181046

theorem fullRecordGapTerm04622_eq_value :
    recordGapCenter + 181046 = fullRecordGapValue04622 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04622_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04622 (fullRecordGapValue04622 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04622_not_prime : ¬(recordGapCenter + 181046).Prime := by
  rw [fullRecordGapTerm04622_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04622, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04622_fast_pow_mod_ne_one

def fullRecordGapValue04623 : Nat := fullRecordGapCenterValue + 181052

theorem fullRecordGapTerm04623_eq_value :
    recordGapCenter + 181052 = fullRecordGapValue04623 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04623_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04623 (fullRecordGapValue04623 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04623_not_prime : ¬(recordGapCenter + 181052).Prime := by
  rw [fullRecordGapTerm04623_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04623, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04623_fast_pow_mod_ne_one

def fullRecordGapValue04624 : Nat := fullRecordGapCenterValue + 181238

theorem fullRecordGapTerm04624_eq_value :
    recordGapCenter + 181238 = fullRecordGapValue04624 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04624_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04624 (fullRecordGapValue04624 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04624_not_prime : ¬(recordGapCenter + 181238).Prime := by
  rw [fullRecordGapTerm04624_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04624, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04624_fast_pow_mod_ne_one

def fullRecordGapValue04625 : Nat := fullRecordGapCenterValue + 181406

theorem fullRecordGapTerm04625_eq_value :
    recordGapCenter + 181406 = fullRecordGapValue04625 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04625_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04625 (fullRecordGapValue04625 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04625_not_prime : ¬(recordGapCenter + 181406).Prime := by
  rw [fullRecordGapTerm04625_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04625, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04625_fast_pow_mod_ne_one

def fullRecordGapValue04626 : Nat := fullRecordGapCenterValue + 181646

theorem fullRecordGapTerm04626_eq_value :
    recordGapCenter + 181646 = fullRecordGapValue04626 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04626_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04626 (fullRecordGapValue04626 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04626_not_prime : ¬(recordGapCenter + 181646).Prime := by
  rw [fullRecordGapTerm04626_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04626, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04626_fast_pow_mod_ne_one

def fullRecordGapValue04627 : Nat := fullRecordGapCenterValue + 181682

theorem fullRecordGapTerm04627_eq_value :
    recordGapCenter + 181682 = fullRecordGapValue04627 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04627_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04627 (fullRecordGapValue04627 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04627_not_prime : ¬(recordGapCenter + 181682).Prime := by
  rw [fullRecordGapTerm04627_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04627, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04627_fast_pow_mod_ne_one

def fullRecordGapValue04628 : Nat := fullRecordGapCenterValue + 181988

theorem fullRecordGapTerm04628_eq_value :
    recordGapCenter + 181988 = fullRecordGapValue04628 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04628_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04628 (fullRecordGapValue04628 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04628_not_prime : ¬(recordGapCenter + 181988).Prime := by
  rw [fullRecordGapTerm04628_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04628, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04628_fast_pow_mod_ne_one

def fullRecordGapValue04629 : Nat := fullRecordGapCenterValue + 182018

theorem fullRecordGapTerm04629_eq_value :
    recordGapCenter + 182018 = fullRecordGapValue04629 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04629_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04629 (fullRecordGapValue04629 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04629_not_prime : ¬(recordGapCenter + 182018).Prime := by
  rw [fullRecordGapTerm04629_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04629, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04629_fast_pow_mod_ne_one

def fullRecordGapValue04630 : Nat := fullRecordGapCenterValue + 182162

theorem fullRecordGapTerm04630_eq_value :
    recordGapCenter + 182162 = fullRecordGapValue04630 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04630_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04630 (fullRecordGapValue04630 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04630_not_prime : ¬(recordGapCenter + 182162).Prime := by
  rw [fullRecordGapTerm04630_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04630, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04630_fast_pow_mod_ne_one

def fullRecordGapValue04631 : Nat := fullRecordGapCenterValue + 182198

theorem fullRecordGapTerm04631_eq_value :
    recordGapCenter + 182198 = fullRecordGapValue04631 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04631_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04631 (fullRecordGapValue04631 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04631_not_prime : ¬(recordGapCenter + 182198).Prime := by
  rw [fullRecordGapTerm04631_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04631, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04631_fast_pow_mod_ne_one

def fullRecordGapValue04632 : Nat := fullRecordGapCenterValue + 182228

theorem fullRecordGapTerm04632_eq_value :
    recordGapCenter + 182228 = fullRecordGapValue04632 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04632_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04632 (fullRecordGapValue04632 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04632_not_prime : ¬(recordGapCenter + 182228).Prime := by
  rw [fullRecordGapTerm04632_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04632, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04632_fast_pow_mod_ne_one

def fullRecordGapValue04633 : Nat := fullRecordGapCenterValue + 182306

theorem fullRecordGapTerm04633_eq_value :
    recordGapCenter + 182306 = fullRecordGapValue04633 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04633_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04633 (fullRecordGapValue04633 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04633_not_prime : ¬(recordGapCenter + 182306).Prime := by
  rw [fullRecordGapTerm04633_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04633, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04633_fast_pow_mod_ne_one

def fullRecordGapValue04634 : Nat := fullRecordGapCenterValue + 182396

theorem fullRecordGapTerm04634_eq_value :
    recordGapCenter + 182396 = fullRecordGapValue04634 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04634_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04634 (fullRecordGapValue04634 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04634_not_prime : ¬(recordGapCenter + 182396).Prime := by
  rw [fullRecordGapTerm04634_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04634, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04634_fast_pow_mod_ne_one

def fullRecordGapValue04635 : Nat := fullRecordGapCenterValue + 182498

theorem fullRecordGapTerm04635_eq_value :
    recordGapCenter + 182498 = fullRecordGapValue04635 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04635_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04635 (fullRecordGapValue04635 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04635_not_prime : ¬(recordGapCenter + 182498).Prime := by
  rw [fullRecordGapTerm04635_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04635, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04635_fast_pow_mod_ne_one

def fullRecordGapValue04636 : Nat := fullRecordGapCenterValue + 182582

theorem fullRecordGapTerm04636_eq_value :
    recordGapCenter + 182582 = fullRecordGapValue04636 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04636_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04636 (fullRecordGapValue04636 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04636_not_prime : ¬(recordGapCenter + 182582).Prime := by
  rw [fullRecordGapTerm04636_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04636, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04636_fast_pow_mod_ne_one

def fullRecordGapValue04637 : Nat := fullRecordGapCenterValue + 182738

theorem fullRecordGapTerm04637_eq_value :
    recordGapCenter + 182738 = fullRecordGapValue04637 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04637_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04637 (fullRecordGapValue04637 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04637_not_prime : ¬(recordGapCenter + 182738).Prime := by
  rw [fullRecordGapTerm04637_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04637, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04637_fast_pow_mod_ne_one

def fullRecordGapValue04638 : Nat := fullRecordGapCenterValue + 182828

theorem fullRecordGapTerm04638_eq_value :
    recordGapCenter + 182828 = fullRecordGapValue04638 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04638_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04638 (fullRecordGapValue04638 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04638_not_prime : ¬(recordGapCenter + 182828).Prime := by
  rw [fullRecordGapTerm04638_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04638, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04638_fast_pow_mod_ne_one

def fullRecordGapValue04639 : Nat := fullRecordGapCenterValue + 182906

theorem fullRecordGapTerm04639_eq_value :
    recordGapCenter + 182906 = fullRecordGapValue04639 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04639_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04639 (fullRecordGapValue04639 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04639_not_prime : ¬(recordGapCenter + 182906).Prime := by
  rw [fullRecordGapTerm04639_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04639, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04639_fast_pow_mod_ne_one

def fullRecordGapValue04640 : Nat := fullRecordGapCenterValue + 182918

theorem fullRecordGapTerm04640_eq_value :
    recordGapCenter + 182918 = fullRecordGapValue04640 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04640_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04640 (fullRecordGapValue04640 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04640_not_prime : ¬(recordGapCenter + 182918).Prime := by
  rw [fullRecordGapTerm04640_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04640, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04640_fast_pow_mod_ne_one

def fullRecordGapValue04641 : Nat := fullRecordGapCenterValue + 182952

theorem fullRecordGapTerm04641_eq_value :
    recordGapCenter + 182952 = fullRecordGapValue04641 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04641_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04641 (fullRecordGapValue04641 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04641_not_prime : ¬(recordGapCenter + 182952).Prime := by
  rw [fullRecordGapTerm04641_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04641, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04641_fast_pow_mod_ne_one

def fullRecordGapValue04642 : Nat := fullRecordGapCenterValue + 183026

theorem fullRecordGapTerm04642_eq_value :
    recordGapCenter + 183026 = fullRecordGapValue04642 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04642_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04642 (fullRecordGapValue04642 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04642_not_prime : ¬(recordGapCenter + 183026).Prime := by
  rw [fullRecordGapTerm04642_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04642, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04642_fast_pow_mod_ne_one

def fullRecordGapValue04643 : Nat := fullRecordGapCenterValue + 183068

theorem fullRecordGapTerm04643_eq_value :
    recordGapCenter + 183068 = fullRecordGapValue04643 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04643_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04643 (fullRecordGapValue04643 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04643_not_prime : ¬(recordGapCenter + 183068).Prime := by
  rw [fullRecordGapTerm04643_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04643, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04643_fast_pow_mod_ne_one

def fullRecordGapValue04644 : Nat := fullRecordGapCenterValue + 183332

theorem fullRecordGapTerm04644_eq_value :
    recordGapCenter + 183332 = fullRecordGapValue04644 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04644_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04644 (fullRecordGapValue04644 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04644_not_prime : ¬(recordGapCenter + 183332).Prime := by
  rw [fullRecordGapTerm04644_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04644, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04644_fast_pow_mod_ne_one

def fullRecordGapValue04645 : Nat := fullRecordGapCenterValue + 183422

theorem fullRecordGapTerm04645_eq_value :
    recordGapCenter + 183422 = fullRecordGapValue04645 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04645_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04645 (fullRecordGapValue04645 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04645_not_prime : ¬(recordGapCenter + 183422).Prime := by
  rw [fullRecordGapTerm04645_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04645, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04645_fast_pow_mod_ne_one

def fullRecordGapValue04646 : Nat := fullRecordGapCenterValue + 183626

theorem fullRecordGapTerm04646_eq_value :
    recordGapCenter + 183626 = fullRecordGapValue04646 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04646_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04646 (fullRecordGapValue04646 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04646_not_prime : ¬(recordGapCenter + 183626).Prime := by
  rw [fullRecordGapTerm04646_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04646, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04646_fast_pow_mod_ne_one

def fullRecordGapValue04647 : Nat := fullRecordGapCenterValue + 183750

theorem fullRecordGapTerm04647_eq_value :
    recordGapCenter + 183750 = fullRecordGapValue04647 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04647_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04647 (fullRecordGapValue04647 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04647_not_prime : ¬(recordGapCenter + 183750).Prime := by
  rw [fullRecordGapTerm04647_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04647, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04647_fast_pow_mod_ne_one

def fullRecordGapValue04648 : Nat := fullRecordGapCenterValue + 183818

theorem fullRecordGapTerm04648_eq_value :
    recordGapCenter + 183818 = fullRecordGapValue04648 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04648_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04648 (fullRecordGapValue04648 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04648_not_prime : ¬(recordGapCenter + 183818).Prime := by
  rw [fullRecordGapTerm04648_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04648, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04648_fast_pow_mod_ne_one

def fullRecordGapValue04649 : Nat := fullRecordGapCenterValue + 183956

theorem fullRecordGapTerm04649_eq_value :
    recordGapCenter + 183956 = fullRecordGapValue04649 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04649_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04649 (fullRecordGapValue04649 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04649_not_prime : ¬(recordGapCenter + 183956).Prime := by
  rw [fullRecordGapTerm04649_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04649, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04649_fast_pow_mod_ne_one

def fullRecordGapValue04650 : Nat := fullRecordGapCenterValue + 184166

theorem fullRecordGapTerm04650_eq_value :
    recordGapCenter + 184166 = fullRecordGapValue04650 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04650_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04650 (fullRecordGapValue04650 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04650_not_prime : ¬(recordGapCenter + 184166).Prime := by
  rw [fullRecordGapTerm04650_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04650, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04650_fast_pow_mod_ne_one

def fullRecordGapValue04651 : Nat := fullRecordGapCenterValue + 184196

theorem fullRecordGapTerm04651_eq_value :
    recordGapCenter + 184196 = fullRecordGapValue04651 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04651_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04651 (fullRecordGapValue04651 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04651_not_prime : ¬(recordGapCenter + 184196).Prime := by
  rw [fullRecordGapTerm04651_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04651, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04651_fast_pow_mod_ne_one

def fullRecordGapValue04652 : Nat := fullRecordGapCenterValue + 184238

theorem fullRecordGapTerm04652_eq_value :
    recordGapCenter + 184238 = fullRecordGapValue04652 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04652_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04652 (fullRecordGapValue04652 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04652_not_prime : ¬(recordGapCenter + 184238).Prime := by
  rw [fullRecordGapTerm04652_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04652, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04652_fast_pow_mod_ne_one

def fullRecordGapValue04653 : Nat := fullRecordGapCenterValue + 184286

theorem fullRecordGapTerm04653_eq_value :
    recordGapCenter + 184286 = fullRecordGapValue04653 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04653_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04653 (fullRecordGapValue04653 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04653_not_prime : ¬(recordGapCenter + 184286).Prime := by
  rw [fullRecordGapTerm04653_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04653, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04653_fast_pow_mod_ne_one

def fullRecordGapValue04654 : Nat := fullRecordGapCenterValue + 184320

theorem fullRecordGapTerm04654_eq_value :
    recordGapCenter + 184320 = fullRecordGapValue04654 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04654_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04654 (fullRecordGapValue04654 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04654_not_prime : ¬(recordGapCenter + 184320).Prime := by
  rw [fullRecordGapTerm04654_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04654, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04654_fast_pow_mod_ne_one

def fullRecordGapValue04655 : Nat := fullRecordGapCenterValue + 184406

theorem fullRecordGapTerm04655_eq_value :
    recordGapCenter + 184406 = fullRecordGapValue04655 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04655_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04655 (fullRecordGapValue04655 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04655_not_prime : ¬(recordGapCenter + 184406).Prime := by
  rw [fullRecordGapTerm04655_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04655, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04655_fast_pow_mod_ne_one

def fullRecordGapValue04656 : Nat := fullRecordGapCenterValue + 184502

theorem fullRecordGapTerm04656_eq_value :
    recordGapCenter + 184502 = fullRecordGapValue04656 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04656_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04656 (fullRecordGapValue04656 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04656_not_prime : ¬(recordGapCenter + 184502).Prime := by
  rw [fullRecordGapTerm04656_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04656, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04656_fast_pow_mod_ne_one

def fullRecordGapValue04657 : Nat := fullRecordGapCenterValue + 184538

theorem fullRecordGapTerm04657_eq_value :
    recordGapCenter + 184538 = fullRecordGapValue04657 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04657_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04657 (fullRecordGapValue04657 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04657_not_prime : ¬(recordGapCenter + 184538).Prime := by
  rw [fullRecordGapTerm04657_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04657, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04657_fast_pow_mod_ne_one

def fullRecordGapValue04658 : Nat := fullRecordGapCenterValue + 184622

theorem fullRecordGapTerm04658_eq_value :
    recordGapCenter + 184622 = fullRecordGapValue04658 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04658_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04658 (fullRecordGapValue04658 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04658_not_prime : ¬(recordGapCenter + 184622).Prime := by
  rw [fullRecordGapTerm04658_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04658, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04658_fast_pow_mod_ne_one

def fullRecordGapValue04659 : Nat := fullRecordGapCenterValue + 184800

theorem fullRecordGapTerm04659_eq_value :
    recordGapCenter + 184800 = fullRecordGapValue04659 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04659_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04659 (fullRecordGapValue04659 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04659_not_prime : ¬(recordGapCenter + 184800).Prime := by
  rw [fullRecordGapTerm04659_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04659, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04659_fast_pow_mod_ne_one

def fullRecordGapValue04660 : Nat := fullRecordGapCenterValue + 184916

theorem fullRecordGapTerm04660_eq_value :
    recordGapCenter + 184916 = fullRecordGapValue04660 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04660_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04660 (fullRecordGapValue04660 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04660_not_prime : ¬(recordGapCenter + 184916).Prime := by
  rw [fullRecordGapTerm04660_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04660, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04660_fast_pow_mod_ne_one

def fullRecordGapValue04661 : Nat := fullRecordGapCenterValue + 185006

theorem fullRecordGapTerm04661_eq_value :
    recordGapCenter + 185006 = fullRecordGapValue04661 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04661_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04661 (fullRecordGapValue04661 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04661_not_prime : ¬(recordGapCenter + 185006).Prime := by
  rw [fullRecordGapTerm04661_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04661, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04661_fast_pow_mod_ne_one

def fullRecordGapValue04662 : Nat := fullRecordGapCenterValue + 185102

theorem fullRecordGapTerm04662_eq_value :
    recordGapCenter + 185102 = fullRecordGapValue04662 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04662_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04662 (fullRecordGapValue04662 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04662_not_prime : ¬(recordGapCenter + 185102).Prime := by
  rw [fullRecordGapTerm04662_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04662, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04662_fast_pow_mod_ne_one

def fullRecordGapValue04663 : Nat := fullRecordGapCenterValue + 185220

theorem fullRecordGapTerm04663_eq_value :
    recordGapCenter + 185220 = fullRecordGapValue04663 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04663_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04663 (fullRecordGapValue04663 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04663_not_prime : ¬(recordGapCenter + 185220).Prime := by
  rw [fullRecordGapTerm04663_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04663, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04663_fast_pow_mod_ne_one

def fullRecordGapValue04664 : Nat := fullRecordGapCenterValue + 185348

theorem fullRecordGapTerm04664_eq_value :
    recordGapCenter + 185348 = fullRecordGapValue04664 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04664_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04664 (fullRecordGapValue04664 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04664_not_prime : ¬(recordGapCenter + 185348).Prime := by
  rw [fullRecordGapTerm04664_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04664, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04664_fast_pow_mod_ne_one

def fullRecordGapValue04665 : Nat := fullRecordGapCenterValue + 185582

theorem fullRecordGapTerm04665_eq_value :
    recordGapCenter + 185582 = fullRecordGapValue04665 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04665_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04665 (fullRecordGapValue04665 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04665_not_prime : ¬(recordGapCenter + 185582).Prime := by
  rw [fullRecordGapTerm04665_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04665, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04665_fast_pow_mod_ne_one

def fullRecordGapValue04666 : Nat := fullRecordGapCenterValue + 185756

theorem fullRecordGapTerm04666_eq_value :
    recordGapCenter + 185756 = fullRecordGapValue04666 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04666_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04666 (fullRecordGapValue04666 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04666_not_prime : ¬(recordGapCenter + 185756).Prime := by
  rw [fullRecordGapTerm04666_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04666, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04666_fast_pow_mod_ne_one

def fullRecordGapValue04667 : Nat := fullRecordGapCenterValue + 185798

theorem fullRecordGapTerm04667_eq_value :
    recordGapCenter + 185798 = fullRecordGapValue04667 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04667_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04667 (fullRecordGapValue04667 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04667_not_prime : ¬(recordGapCenter + 185798).Prime := by
  rw [fullRecordGapTerm04667_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04667, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04667_fast_pow_mod_ne_one

def fullRecordGapValue04668 : Nat := fullRecordGapCenterValue + 186092

theorem fullRecordGapTerm04668_eq_value :
    recordGapCenter + 186092 = fullRecordGapValue04668 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04668_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04668 (fullRecordGapValue04668 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04668_not_prime : ¬(recordGapCenter + 186092).Prime := by
  rw [fullRecordGapTerm04668_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04668, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04668_fast_pow_mod_ne_one

def fullRecordGapValue04669 : Nat := fullRecordGapCenterValue + 186266

theorem fullRecordGapTerm04669_eq_value :
    recordGapCenter + 186266 = fullRecordGapValue04669 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04669_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04669 (fullRecordGapValue04669 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04669_not_prime : ¬(recordGapCenter + 186266).Prime := by
  rw [fullRecordGapTerm04669_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04669, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04669_fast_pow_mod_ne_one

def fullRecordGapValue04670 : Nat := fullRecordGapCenterValue + 186278

theorem fullRecordGapTerm04670_eq_value :
    recordGapCenter + 186278 = fullRecordGapValue04670 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04670_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04670 (fullRecordGapValue04670 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04670_not_prime : ¬(recordGapCenter + 186278).Prime := by
  rw [fullRecordGapTerm04670_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04670, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04670_fast_pow_mod_ne_one

def fullRecordGapValue04671 : Nat := fullRecordGapCenterValue + 186302

theorem fullRecordGapTerm04671_eq_value :
    recordGapCenter + 186302 = fullRecordGapValue04671 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04671_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04671 (fullRecordGapValue04671 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04671_not_prime : ¬(recordGapCenter + 186302).Prime := by
  rw [fullRecordGapTerm04671_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04671, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04671_fast_pow_mod_ne_one

def fullRecordGapValue04672 : Nat := fullRecordGapCenterValue + 186398

theorem fullRecordGapTerm04672_eq_value :
    recordGapCenter + 186398 = fullRecordGapValue04672 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04672_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04672 (fullRecordGapValue04672 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04672_not_prime : ¬(recordGapCenter + 186398).Prime := by
  rw [fullRecordGapTerm04672_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04672, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04672_fast_pow_mod_ne_one

def fullRecordGapValue04673 : Nat := fullRecordGapCenterValue + 186476

theorem fullRecordGapTerm04673_eq_value :
    recordGapCenter + 186476 = fullRecordGapValue04673 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04673_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04673 (fullRecordGapValue04673 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04673_not_prime : ¬(recordGapCenter + 186476).Prime := by
  rw [fullRecordGapTerm04673_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04673, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04673_fast_pow_mod_ne_one

def fullRecordGapValue04674 : Nat := fullRecordGapCenterValue + 186482

theorem fullRecordGapTerm04674_eq_value :
    recordGapCenter + 186482 = fullRecordGapValue04674 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04674_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04674 (fullRecordGapValue04674 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04674_not_prime : ¬(recordGapCenter + 186482).Prime := by
  rw [fullRecordGapTerm04674_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04674, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04674_fast_pow_mod_ne_one

def fullRecordGapValue04675 : Nat := fullRecordGapCenterValue + 186566

theorem fullRecordGapTerm04675_eq_value :
    recordGapCenter + 186566 = fullRecordGapValue04675 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04675_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04675 (fullRecordGapValue04675 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04675_not_prime : ¬(recordGapCenter + 186566).Prime := by
  rw [fullRecordGapTerm04675_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04675, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04675_fast_pow_mod_ne_one

def fullRecordGapValue04676 : Nat := fullRecordGapCenterValue + 186716

theorem fullRecordGapTerm04676_eq_value :
    recordGapCenter + 186716 = fullRecordGapValue04676 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04676_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04676 (fullRecordGapValue04676 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04676_not_prime : ¬(recordGapCenter + 186716).Prime := by
  rw [fullRecordGapTerm04676_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04676, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04676_fast_pow_mod_ne_one

def fullRecordGapValue04677 : Nat := fullRecordGapCenterValue + 186812

theorem fullRecordGapTerm04677_eq_value :
    recordGapCenter + 186812 = fullRecordGapValue04677 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04677_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04677 (fullRecordGapValue04677 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04677_not_prime : ¬(recordGapCenter + 186812).Prime := by
  rw [fullRecordGapTerm04677_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04677, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04677_fast_pow_mod_ne_one

def fullRecordGapValue04678 : Nat := fullRecordGapCenterValue + 187028

theorem fullRecordGapTerm04678_eq_value :
    recordGapCenter + 187028 = fullRecordGapValue04678 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04678_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04678 (fullRecordGapValue04678 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04678_not_prime : ¬(recordGapCenter + 187028).Prime := by
  rw [fullRecordGapTerm04678_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04678, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04678_fast_pow_mod_ne_one

def fullRecordGapValue04679 : Nat := fullRecordGapCenterValue + 187076

theorem fullRecordGapTerm04679_eq_value :
    recordGapCenter + 187076 = fullRecordGapValue04679 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04679_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04679 (fullRecordGapValue04679 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04679_not_prime : ¬(recordGapCenter + 187076).Prime := by
  rw [fullRecordGapTerm04679_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04679, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04679_fast_pow_mod_ne_one

def fullRecordGapValue04680 : Nat := fullRecordGapCenterValue + 187118

theorem fullRecordGapTerm04680_eq_value :
    recordGapCenter + 187118 = fullRecordGapValue04680 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04680_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04680 (fullRecordGapValue04680 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04680_not_prime : ¬(recordGapCenter + 187118).Prime := by
  rw [fullRecordGapTerm04680_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04680, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04680_fast_pow_mod_ne_one

def fullRecordGapValue04681 : Nat := fullRecordGapCenterValue + 187316

theorem fullRecordGapTerm04681_eq_value :
    recordGapCenter + 187316 = fullRecordGapValue04681 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04681_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04681 (fullRecordGapValue04681 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04681_not_prime : ¬(recordGapCenter + 187316).Prime := by
  rw [fullRecordGapTerm04681_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04681, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04681_fast_pow_mod_ne_one

def fullRecordGapValue04682 : Nat := fullRecordGapCenterValue + 187500

theorem fullRecordGapTerm04682_eq_value :
    recordGapCenter + 187500 = fullRecordGapValue04682 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04682_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04682 (fullRecordGapValue04682 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04682_not_prime : ¬(recordGapCenter + 187500).Prime := by
  rw [fullRecordGapTerm04682_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04682, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04682_fast_pow_mod_ne_one

def fullRecordGapValue04683 : Nat := fullRecordGapCenterValue + 187556

theorem fullRecordGapTerm04683_eq_value :
    recordGapCenter + 187556 = fullRecordGapValue04683 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04683_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04683 (fullRecordGapValue04683 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04683_not_prime : ¬(recordGapCenter + 187556).Prime := by
  rw [fullRecordGapTerm04683_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04683, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04683_fast_pow_mod_ne_one

def fullRecordGapValue04684 : Nat := fullRecordGapCenterValue + 187826

theorem fullRecordGapTerm04684_eq_value :
    recordGapCenter + 187826 = fullRecordGapValue04684 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04684_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04684 (fullRecordGapValue04684 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04684_not_prime : ¬(recordGapCenter + 187826).Prime := by
  rw [fullRecordGapTerm04684_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04684, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04684_fast_pow_mod_ne_one

def fullRecordGapValue04685 : Nat := fullRecordGapCenterValue + 188126

theorem fullRecordGapTerm04685_eq_value :
    recordGapCenter + 188126 = fullRecordGapValue04685 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04685_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04685 (fullRecordGapValue04685 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04685_not_prime : ¬(recordGapCenter + 188126).Prime := by
  rw [fullRecordGapTerm04685_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04685, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04685_fast_pow_mod_ne_one

def fullRecordGapValue04686 : Nat := fullRecordGapCenterValue + 188160

theorem fullRecordGapTerm04686_eq_value :
    recordGapCenter + 188160 = fullRecordGapValue04686 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04686_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04686 (fullRecordGapValue04686 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04686_not_prime : ¬(recordGapCenter + 188160).Prime := by
  rw [fullRecordGapTerm04686_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04686, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04686_fast_pow_mod_ne_one

def fullRecordGapValue04687 : Nat := fullRecordGapCenterValue + 188372

theorem fullRecordGapTerm04687_eq_value :
    recordGapCenter + 188372 = fullRecordGapValue04687 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04687_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04687 (fullRecordGapValue04687 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04687_not_prime : ¬(recordGapCenter + 188372).Prime := by
  rw [fullRecordGapTerm04687_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04687, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04687_fast_pow_mod_ne_one

def fullRecordGapValue04688 : Nat := fullRecordGapCenterValue + 188522

theorem fullRecordGapTerm04688_eq_value :
    recordGapCenter + 188522 = fullRecordGapValue04688 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04688_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04688 (fullRecordGapValue04688 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04688_not_prime : ¬(recordGapCenter + 188522).Prime := by
  rw [fullRecordGapTerm04688_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04688, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04688_fast_pow_mod_ne_one

def fullRecordGapValue04689 : Nat := fullRecordGapCenterValue + 188582

theorem fullRecordGapTerm04689_eq_value :
    recordGapCenter + 188582 = fullRecordGapValue04689 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04689_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04689 (fullRecordGapValue04689 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04689_not_prime : ¬(recordGapCenter + 188582).Prime := by
  rw [fullRecordGapTerm04689_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04689, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04689_fast_pow_mod_ne_one

def fullRecordGapValue04690 : Nat := fullRecordGapCenterValue + 188588

theorem fullRecordGapTerm04690_eq_value :
    recordGapCenter + 188588 = fullRecordGapValue04690 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04690_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04690 (fullRecordGapValue04690 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04690_not_prime : ¬(recordGapCenter + 188588).Prime := by
  rw [fullRecordGapTerm04690_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04690, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04690_fast_pow_mod_ne_one

def fullRecordGapValue04691 : Nat := fullRecordGapCenterValue + 188618

theorem fullRecordGapTerm04691_eq_value :
    recordGapCenter + 188618 = fullRecordGapValue04691 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04691_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04691 (fullRecordGapValue04691 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04691_not_prime : ¬(recordGapCenter + 188618).Prime := by
  rw [fullRecordGapTerm04691_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04691, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04691_fast_pow_mod_ne_one

def fullRecordGapValue04692 : Nat := fullRecordGapCenterValue + 188882

theorem fullRecordGapTerm04692_eq_value :
    recordGapCenter + 188882 = fullRecordGapValue04692 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04692_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04692 (fullRecordGapValue04692 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04692_not_prime : ¬(recordGapCenter + 188882).Prime := by
  rw [fullRecordGapTerm04692_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04692, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04692_fast_pow_mod_ne_one

def fullRecordGapValue04693 : Nat := fullRecordGapCenterValue + 188948

theorem fullRecordGapTerm04693_eq_value :
    recordGapCenter + 188948 = fullRecordGapValue04693 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04693_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04693 (fullRecordGapValue04693 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04693_not_prime : ¬(recordGapCenter + 188948).Prime := by
  rw [fullRecordGapTerm04693_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04693, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04693_fast_pow_mod_ne_one

def fullRecordGapValue04694 : Nat := fullRecordGapCenterValue + 188966

theorem fullRecordGapTerm04694_eq_value :
    recordGapCenter + 188966 = fullRecordGapValue04694 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04694_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04694 (fullRecordGapValue04694 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04694_not_prime : ¬(recordGapCenter + 188966).Prime := by
  rw [fullRecordGapTerm04694_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04694, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04694_fast_pow_mod_ne_one

def fullRecordGapValue04695 : Nat := fullRecordGapCenterValue + 189206

theorem fullRecordGapTerm04695_eq_value :
    recordGapCenter + 189206 = fullRecordGapValue04695 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04695_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04695 (fullRecordGapValue04695 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04695_not_prime : ¬(recordGapCenter + 189206).Prime := by
  rw [fullRecordGapTerm04695_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04695, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04695_fast_pow_mod_ne_one

def fullRecordGapValue04696 : Nat := fullRecordGapCenterValue + 189236

theorem fullRecordGapTerm04696_eq_value :
    recordGapCenter + 189236 = fullRecordGapValue04696 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04696_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04696 (fullRecordGapValue04696 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04696_not_prime : ¬(recordGapCenter + 189236).Prime := by
  rw [fullRecordGapTerm04696_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04696, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04696_fast_pow_mod_ne_one

def fullRecordGapValue04697 : Nat := fullRecordGapCenterValue + 189302

theorem fullRecordGapTerm04697_eq_value :
    recordGapCenter + 189302 = fullRecordGapValue04697 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04697_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04697 (fullRecordGapValue04697 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04697_not_prime : ¬(recordGapCenter + 189302).Prime := by
  rw [fullRecordGapTerm04697_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04697, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04697_fast_pow_mod_ne_one

def fullRecordGapValue04698 : Nat := fullRecordGapCenterValue + 189446

theorem fullRecordGapTerm04698_eq_value :
    recordGapCenter + 189446 = fullRecordGapValue04698 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04698_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04698 (fullRecordGapValue04698 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04698_not_prime : ¬(recordGapCenter + 189446).Prime := by
  rw [fullRecordGapTerm04698_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04698, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04698_fast_pow_mod_ne_one

def fullRecordGapValue04699 : Nat := fullRecordGapCenterValue + 189542

theorem fullRecordGapTerm04699_eq_value :
    recordGapCenter + 189542 = fullRecordGapValue04699 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04699_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04699 (fullRecordGapValue04699 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04699_not_prime : ¬(recordGapCenter + 189542).Prime := by
  rw [fullRecordGapTerm04699_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04699, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04699_fast_pow_mod_ne_one

def fullRecordGapValue04700 : Nat := fullRecordGapCenterValue + 189638

theorem fullRecordGapTerm04700_eq_value :
    recordGapCenter + 189638 = fullRecordGapValue04700 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04700_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04700 (fullRecordGapValue04700 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04700_not_prime : ¬(recordGapCenter + 189638).Prime := by
  rw [fullRecordGapTerm04700_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04700, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04700_fast_pow_mod_ne_one

def fullRecordGapValue04701 : Nat := fullRecordGapCenterValue + 189668

theorem fullRecordGapTerm04701_eq_value :
    recordGapCenter + 189668 = fullRecordGapValue04701 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04701_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04701 (fullRecordGapValue04701 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04701_not_prime : ¬(recordGapCenter + 189668).Prime := by
  rw [fullRecordGapTerm04701_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04701, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04701_fast_pow_mod_ne_one

def fullRecordGapValue04702 : Nat := fullRecordGapCenterValue + 189698

theorem fullRecordGapTerm04702_eq_value :
    recordGapCenter + 189698 = fullRecordGapValue04702 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04702_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04702 (fullRecordGapValue04702 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04702_not_prime : ¬(recordGapCenter + 189698).Prime := by
  rw [fullRecordGapTerm04702_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04702, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04702_fast_pow_mod_ne_one

def fullRecordGapValue04703 : Nat := fullRecordGapCenterValue + 189728

theorem fullRecordGapTerm04703_eq_value :
    recordGapCenter + 189728 = fullRecordGapValue04703 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04703_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04703 (fullRecordGapValue04703 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04703_not_prime : ¬(recordGapCenter + 189728).Prime := by
  rw [fullRecordGapTerm04703_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04703, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04703_fast_pow_mod_ne_one

def fullRecordGapValue04704 : Nat := fullRecordGapCenterValue + 190080

theorem fullRecordGapTerm04704_eq_value :
    recordGapCenter + 190080 = fullRecordGapValue04704 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04704_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04704 (fullRecordGapValue04704 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04704_not_prime : ¬(recordGapCenter + 190080).Prime := by
  rw [fullRecordGapTerm04704_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04704, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04704_fast_pow_mod_ne_one

def fullRecordGapValue04705 : Nat := fullRecordGapCenterValue + 190172

theorem fullRecordGapTerm04705_eq_value :
    recordGapCenter + 190172 = fullRecordGapValue04705 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04705_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04705 (fullRecordGapValue04705 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04705_not_prime : ¬(recordGapCenter + 190172).Prime := by
  rw [fullRecordGapTerm04705_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04705, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04705_fast_pow_mod_ne_one

def fullRecordGapValue04706 : Nat := fullRecordGapCenterValue + 190262

theorem fullRecordGapTerm04706_eq_value :
    recordGapCenter + 190262 = fullRecordGapValue04706 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04706_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04706 (fullRecordGapValue04706 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04706_not_prime : ¬(recordGapCenter + 190262).Prime := by
  rw [fullRecordGapTerm04706_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04706, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04706_fast_pow_mod_ne_one

def fullRecordGapValue04707 : Nat := fullRecordGapCenterValue + 190478

theorem fullRecordGapTerm04707_eq_value :
    recordGapCenter + 190478 = fullRecordGapValue04707 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04707_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04707 (fullRecordGapValue04707 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04707_not_prime : ¬(recordGapCenter + 190478).Prime := by
  rw [fullRecordGapTerm04707_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04707, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04707_fast_pow_mod_ne_one

def fullRecordGapValue04708 : Nat := fullRecordGapCenterValue + 190556

theorem fullRecordGapTerm04708_eq_value :
    recordGapCenter + 190556 = fullRecordGapValue04708 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04708_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04708 (fullRecordGapValue04708 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04708_not_prime : ¬(recordGapCenter + 190556).Prime := by
  rw [fullRecordGapTerm04708_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04708, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04708_fast_pow_mod_ne_one

def fullRecordGapValue04709 : Nat := fullRecordGapCenterValue + 190766

theorem fullRecordGapTerm04709_eq_value :
    recordGapCenter + 190766 = fullRecordGapValue04709 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04709_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04709 (fullRecordGapValue04709 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04709_not_prime : ¬(recordGapCenter + 190766).Prime := by
  rw [fullRecordGapTerm04709_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04709, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04709_fast_pow_mod_ne_one

def fullRecordGapValue04710 : Nat := fullRecordGapCenterValue + 190886

theorem fullRecordGapTerm04710_eq_value :
    recordGapCenter + 190886 = fullRecordGapValue04710 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04710_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04710 (fullRecordGapValue04710 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04710_not_prime : ¬(recordGapCenter + 190886).Prime := by
  rw [fullRecordGapTerm04710_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04710, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04710_fast_pow_mod_ne_one

def fullRecordGapValue04711 : Nat := fullRecordGapCenterValue + 191546

theorem fullRecordGapTerm04711_eq_value :
    recordGapCenter + 191546 = fullRecordGapValue04711 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04711_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04711 (fullRecordGapValue04711 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04711_not_prime : ¬(recordGapCenter + 191546).Prime := by
  rw [fullRecordGapTerm04711_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04711, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04711_fast_pow_mod_ne_one

def fullRecordGapValue04712 : Nat := fullRecordGapCenterValue + 191606

theorem fullRecordGapTerm04712_eq_value :
    recordGapCenter + 191606 = fullRecordGapValue04712 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04712_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04712 (fullRecordGapValue04712 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04712_not_prime : ¬(recordGapCenter + 191606).Prime := by
  rw [fullRecordGapTerm04712_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04712, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04712_fast_pow_mod_ne_one

def fullRecordGapValue04713 : Nat := fullRecordGapCenterValue + 191612

theorem fullRecordGapTerm04713_eq_value :
    recordGapCenter + 191612 = fullRecordGapValue04713 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04713_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04713 (fullRecordGapValue04713 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04713_not_prime : ¬(recordGapCenter + 191612).Prime := by
  rw [fullRecordGapTerm04713_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04713, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04713_fast_pow_mod_ne_one

def fullRecordGapValue04714 : Nat := fullRecordGapCenterValue + 191732

theorem fullRecordGapTerm04714_eq_value :
    recordGapCenter + 191732 = fullRecordGapValue04714 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04714_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04714 (fullRecordGapValue04714 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04714_not_prime : ¬(recordGapCenter + 191732).Prime := by
  rw [fullRecordGapTerm04714_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04714, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04714_fast_pow_mod_ne_one

def fullRecordGapValue04715 : Nat := fullRecordGapCenterValue + 191738

theorem fullRecordGapTerm04715_eq_value :
    recordGapCenter + 191738 = fullRecordGapValue04715 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04715_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04715 (fullRecordGapValue04715 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04715_not_prime : ¬(recordGapCenter + 191738).Prime := by
  rw [fullRecordGapTerm04715_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04715, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04715_fast_pow_mod_ne_one

def fullRecordGapValue04716 : Nat := fullRecordGapCenterValue + 191762

theorem fullRecordGapTerm04716_eq_value :
    recordGapCenter + 191762 = fullRecordGapValue04716 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04716_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04716 (fullRecordGapValue04716 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04716_not_prime : ¬(recordGapCenter + 191762).Prime := by
  rw [fullRecordGapTerm04716_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04716, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04716_fast_pow_mod_ne_one

def fullRecordGapValue04717 : Nat := fullRecordGapCenterValue + 191822

theorem fullRecordGapTerm04717_eq_value :
    recordGapCenter + 191822 = fullRecordGapValue04717 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04717_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04717 (fullRecordGapValue04717 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04717_not_prime : ¬(recordGapCenter + 191822).Prime := by
  rw [fullRecordGapTerm04717_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04717, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04717_fast_pow_mod_ne_one

def fullRecordGapValue04718 : Nat := fullRecordGapCenterValue + 191852

theorem fullRecordGapTerm04718_eq_value :
    recordGapCenter + 191852 = fullRecordGapValue04718 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04718_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04718 (fullRecordGapValue04718 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04718_not_prime : ¬(recordGapCenter + 191852).Prime := by
  rw [fullRecordGapTerm04718_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04718, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04718_fast_pow_mod_ne_one

def fullRecordGapValue04719 : Nat := fullRecordGapCenterValue + 191942

theorem fullRecordGapTerm04719_eq_value :
    recordGapCenter + 191942 = fullRecordGapValue04719 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04719_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04719 (fullRecordGapValue04719 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04719_not_prime : ¬(recordGapCenter + 191942).Prime := by
  rw [fullRecordGapTerm04719_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04719, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04719_fast_pow_mod_ne_one

def fullRecordGapValue04720 : Nat := fullRecordGapCenterValue + 192158

theorem fullRecordGapTerm04720_eq_value :
    recordGapCenter + 192158 = fullRecordGapValue04720 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04720_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04720 (fullRecordGapValue04720 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04720_not_prime : ¬(recordGapCenter + 192158).Prime := by
  rw [fullRecordGapTerm04720_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04720, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04720_fast_pow_mod_ne_one

def fullRecordGapValue04721 : Nat := fullRecordGapCenterValue + 192362

theorem fullRecordGapTerm04721_eq_value :
    recordGapCenter + 192362 = fullRecordGapValue04721 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04721_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04721 (fullRecordGapValue04721 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04721_not_prime : ¬(recordGapCenter + 192362).Prime := by
  rw [fullRecordGapTerm04721_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04721, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04721_fast_pow_mod_ne_one

def fullRecordGapValue04722 : Nat := fullRecordGapCenterValue + 192456

theorem fullRecordGapTerm04722_eq_value :
    recordGapCenter + 192456 = fullRecordGapValue04722 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04722_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04722 (fullRecordGapValue04722 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04722_not_prime : ¬(recordGapCenter + 192456).Prime := by
  rw [fullRecordGapTerm04722_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04722, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04722_fast_pow_mod_ne_one

def fullRecordGapValue04723 : Nat := fullRecordGapCenterValue + 192662

theorem fullRecordGapTerm04723_eq_value :
    recordGapCenter + 192662 = fullRecordGapValue04723 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04723_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04723 (fullRecordGapValue04723 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04723_not_prime : ¬(recordGapCenter + 192662).Prime := by
  rw [fullRecordGapTerm04723_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04723, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04723_fast_pow_mod_ne_one

def fullRecordGapValue04724 : Nat := fullRecordGapCenterValue + 192788

theorem fullRecordGapTerm04724_eq_value :
    recordGapCenter + 192788 = fullRecordGapValue04724 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04724_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04724 (fullRecordGapValue04724 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04724_not_prime : ¬(recordGapCenter + 192788).Prime := by
  rw [fullRecordGapTerm04724_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04724, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04724_fast_pow_mod_ne_one

def fullRecordGapValue04725 : Nat := fullRecordGapCenterValue + 192902

theorem fullRecordGapTerm04725_eq_value :
    recordGapCenter + 192902 = fullRecordGapValue04725 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04725_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04725 (fullRecordGapValue04725 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04725_not_prime : ¬(recordGapCenter + 192902).Prime := by
  rw [fullRecordGapTerm04725_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04725, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04725_fast_pow_mod_ne_one

def fullRecordGapValue04726 : Nat := fullRecordGapCenterValue + 192938

theorem fullRecordGapTerm04726_eq_value :
    recordGapCenter + 192938 = fullRecordGapValue04726 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04726_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04726 (fullRecordGapValue04726 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04726_not_prime : ¬(recordGapCenter + 192938).Prime := by
  rw [fullRecordGapTerm04726_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04726, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04726_fast_pow_mod_ne_one

def fullRecordGapValue04727 : Nat := fullRecordGapCenterValue + 192956

theorem fullRecordGapTerm04727_eq_value :
    recordGapCenter + 192956 = fullRecordGapValue04727 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04727_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04727 (fullRecordGapValue04727 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04727_not_prime : ¬(recordGapCenter + 192956).Prime := by
  rw [fullRecordGapTerm04727_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04727, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04727_fast_pow_mod_ne_one

def fullRecordGapValue04728 : Nat := fullRecordGapCenterValue + 193106

theorem fullRecordGapTerm04728_eq_value :
    recordGapCenter + 193106 = fullRecordGapValue04728 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04728_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04728 (fullRecordGapValue04728 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04728_not_prime : ¬(recordGapCenter + 193106).Prime := by
  rw [fullRecordGapTerm04728_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04728, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04728_fast_pow_mod_ne_one

def fullRecordGapValue04729 : Nat := fullRecordGapCenterValue + 193202

theorem fullRecordGapTerm04729_eq_value :
    recordGapCenter + 193202 = fullRecordGapValue04729 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04729_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04729 (fullRecordGapValue04729 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04729_not_prime : ¬(recordGapCenter + 193202).Prime := by
  rw [fullRecordGapTerm04729_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04729, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04729_fast_pow_mod_ne_one

def fullRecordGapValue04730 : Nat := fullRecordGapCenterValue + 193322

theorem fullRecordGapTerm04730_eq_value :
    recordGapCenter + 193322 = fullRecordGapValue04730 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04730_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04730 (fullRecordGapValue04730 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04730_not_prime : ¬(recordGapCenter + 193322).Prime := by
  rw [fullRecordGapTerm04730_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04730, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04730_fast_pow_mod_ne_one

def fullRecordGapValue04731 : Nat := fullRecordGapCenterValue + 193406

theorem fullRecordGapTerm04731_eq_value :
    recordGapCenter + 193406 = fullRecordGapValue04731 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04731_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04731 (fullRecordGapValue04731 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04731_not_prime : ¬(recordGapCenter + 193406).Prime := by
  rw [fullRecordGapTerm04731_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04731, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04731_fast_pow_mod_ne_one

def fullRecordGapValue04732 : Nat := fullRecordGapCenterValue + 193478

theorem fullRecordGapTerm04732_eq_value :
    recordGapCenter + 193478 = fullRecordGapValue04732 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04732_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04732 (fullRecordGapValue04732 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04732_not_prime : ¬(recordGapCenter + 193478).Prime := by
  rw [fullRecordGapTerm04732_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04732, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04732_fast_pow_mod_ne_one

def fullRecordGapValue04733 : Nat := fullRecordGapCenterValue + 193652

theorem fullRecordGapTerm04733_eq_value :
    recordGapCenter + 193652 = fullRecordGapValue04733 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04733_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04733 (fullRecordGapValue04733 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04733_not_prime : ¬(recordGapCenter + 193652).Prime := by
  rw [fullRecordGapTerm04733_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04733, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04733_fast_pow_mod_ne_one

def fullRecordGapValue04734 : Nat := fullRecordGapCenterValue + 193748

theorem fullRecordGapTerm04734_eq_value :
    recordGapCenter + 193748 = fullRecordGapValue04734 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04734_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04734 (fullRecordGapValue04734 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04734_not_prime : ¬(recordGapCenter + 193748).Prime := by
  rw [fullRecordGapTerm04734_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04734, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04734_fast_pow_mod_ne_one

def fullRecordGapValue04735 : Nat := fullRecordGapCenterValue + 193862

theorem fullRecordGapTerm04735_eq_value :
    recordGapCenter + 193862 = fullRecordGapValue04735 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04735_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04735 (fullRecordGapValue04735 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04735_not_prime : ¬(recordGapCenter + 193862).Prime := by
  rw [fullRecordGapTerm04735_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04735, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04735_fast_pow_mod_ne_one

def fullRecordGapValue04736 : Nat := fullRecordGapCenterValue + 193946

theorem fullRecordGapTerm04736_eq_value :
    recordGapCenter + 193946 = fullRecordGapValue04736 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04736_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04736 (fullRecordGapValue04736 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04736_not_prime : ¬(recordGapCenter + 193946).Prime := by
  rw [fullRecordGapTerm04736_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04736, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04736_fast_pow_mod_ne_one

def fullRecordGapValue04737 : Nat := fullRecordGapCenterValue + 193958

theorem fullRecordGapTerm04737_eq_value :
    recordGapCenter + 193958 = fullRecordGapValue04737 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04737_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04737 (fullRecordGapValue04737 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04737_not_prime : ¬(recordGapCenter + 193958).Prime := by
  rw [fullRecordGapTerm04737_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04737, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04737_fast_pow_mod_ne_one

def fullRecordGapValue04738 : Nat := fullRecordGapCenterValue + 194006

theorem fullRecordGapTerm04738_eq_value :
    recordGapCenter + 194006 = fullRecordGapValue04738 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04738_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04738 (fullRecordGapValue04738 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04738_not_prime : ¬(recordGapCenter + 194006).Prime := by
  rw [fullRecordGapTerm04738_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04738, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04738_fast_pow_mod_ne_one

def fullRecordGapValue04739 : Nat := fullRecordGapCenterValue + 194042

theorem fullRecordGapTerm04739_eq_value :
    recordGapCenter + 194042 = fullRecordGapValue04739 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04739_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04739 (fullRecordGapValue04739 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04739_not_prime : ¬(recordGapCenter + 194042).Prime := by
  rw [fullRecordGapTerm04739_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04739, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04739_fast_pow_mod_ne_one

def fullRecordGapValue04740 : Nat := fullRecordGapCenterValue + 194108

theorem fullRecordGapTerm04740_eq_value :
    recordGapCenter + 194108 = fullRecordGapValue04740 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04740_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04740 (fullRecordGapValue04740 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04740_not_prime : ¬(recordGapCenter + 194108).Prime := by
  rw [fullRecordGapTerm04740_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04740, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04740_fast_pow_mod_ne_one

def fullRecordGapValue04741 : Nat := fullRecordGapCenterValue + 194156

theorem fullRecordGapTerm04741_eq_value :
    recordGapCenter + 194156 = fullRecordGapValue04741 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04741_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04741 (fullRecordGapValue04741 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04741_not_prime : ¬(recordGapCenter + 194156).Prime := by
  rw [fullRecordGapTerm04741_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04741, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04741_fast_pow_mod_ne_one

def fullRecordGapValue04742 : Nat := fullRecordGapCenterValue + 194162

theorem fullRecordGapTerm04742_eq_value :
    recordGapCenter + 194162 = fullRecordGapValue04742 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04742_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04742 (fullRecordGapValue04742 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04742_not_prime : ¬(recordGapCenter + 194162).Prime := by
  rw [fullRecordGapTerm04742_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04742, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04742_fast_pow_mod_ne_one

def fullRecordGapValue04743 : Nat := fullRecordGapCenterValue + 194252

theorem fullRecordGapTerm04743_eq_value :
    recordGapCenter + 194252 = fullRecordGapValue04743 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04743_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04743 (fullRecordGapValue04743 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04743_not_prime : ¬(recordGapCenter + 194252).Prime := by
  rw [fullRecordGapTerm04743_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04743, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04743_fast_pow_mod_ne_one

def fullRecordGapValue04744 : Nat := fullRecordGapCenterValue + 194318

theorem fullRecordGapTerm04744_eq_value :
    recordGapCenter + 194318 = fullRecordGapValue04744 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04744_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04744 (fullRecordGapValue04744 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04744_not_prime : ¬(recordGapCenter + 194318).Prime := by
  rw [fullRecordGapTerm04744_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04744, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04744_fast_pow_mod_ne_one

def fullRecordGapValue04745 : Nat := fullRecordGapCenterValue + 194342

theorem fullRecordGapTerm04745_eq_value :
    recordGapCenter + 194342 = fullRecordGapValue04745 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04745_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04745 (fullRecordGapValue04745 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04745_not_prime : ¬(recordGapCenter + 194342).Prime := by
  rw [fullRecordGapTerm04745_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04745, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04745_fast_pow_mod_ne_one

def fullRecordGapValue04746 : Nat := fullRecordGapCenterValue + 194372

theorem fullRecordGapTerm04746_eq_value :
    recordGapCenter + 194372 = fullRecordGapValue04746 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04746_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04746 (fullRecordGapValue04746 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04746_not_prime : ¬(recordGapCenter + 194372).Prime := by
  rw [fullRecordGapTerm04746_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04746, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04746_fast_pow_mod_ne_one

def fullRecordGapValue04747 : Nat := fullRecordGapCenterValue + 194400

theorem fullRecordGapTerm04747_eq_value :
    recordGapCenter + 194400 = fullRecordGapValue04747 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04747_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04747 (fullRecordGapValue04747 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04747_not_prime : ¬(recordGapCenter + 194400).Prime := by
  rw [fullRecordGapTerm04747_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04747, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04747_fast_pow_mod_ne_one

def fullRecordGapValue04748 : Nat := fullRecordGapCenterValue + 194462

theorem fullRecordGapTerm04748_eq_value :
    recordGapCenter + 194462 = fullRecordGapValue04748 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04748_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04748 (fullRecordGapValue04748 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04748_not_prime : ¬(recordGapCenter + 194462).Prime := by
  rw [fullRecordGapTerm04748_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04748, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04748_fast_pow_mod_ne_one

def fullRecordGapValue04749 : Nat := fullRecordGapCenterValue + 194588

theorem fullRecordGapTerm04749_eq_value :
    recordGapCenter + 194588 = fullRecordGapValue04749 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04749_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04749 (fullRecordGapValue04749 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04749_not_prime : ¬(recordGapCenter + 194588).Prime := by
  rw [fullRecordGapTerm04749_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04749, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04749_fast_pow_mod_ne_one

def fullRecordGapValue04750 : Nat := fullRecordGapCenterValue + 194846

theorem fullRecordGapTerm04750_eq_value :
    recordGapCenter + 194846 = fullRecordGapValue04750 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04750_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04750 (fullRecordGapValue04750 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04750_not_prime : ¬(recordGapCenter + 194846).Prime := by
  rw [fullRecordGapTerm04750_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04750, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04750_fast_pow_mod_ne_one

def fullRecordGapValue04751 : Nat := fullRecordGapCenterValue + 194882

theorem fullRecordGapTerm04751_eq_value :
    recordGapCenter + 194882 = fullRecordGapValue04751 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04751_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04751 (fullRecordGapValue04751 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04751_not_prime : ¬(recordGapCenter + 194882).Prime := by
  rw [fullRecordGapTerm04751_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04751, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04751_fast_pow_mod_ne_one

def fullRecordGapValue04752 : Nat := fullRecordGapCenterValue + 194906

theorem fullRecordGapTerm04752_eq_value :
    recordGapCenter + 194906 = fullRecordGapValue04752 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04752_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04752 (fullRecordGapValue04752 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04752_not_prime : ¬(recordGapCenter + 194906).Prime := by
  rw [fullRecordGapTerm04752_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04752, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04752_fast_pow_mod_ne_one

def fullRecordGapValue04753 : Nat := fullRecordGapCenterValue + 195122

theorem fullRecordGapTerm04753_eq_value :
    recordGapCenter + 195122 = fullRecordGapValue04753 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04753_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04753 (fullRecordGapValue04753 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04753_not_prime : ¬(recordGapCenter + 195122).Prime := by
  rw [fullRecordGapTerm04753_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04753, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04753_fast_pow_mod_ne_one

def fullRecordGapValue04754 : Nat := fullRecordGapCenterValue + 195218

theorem fullRecordGapTerm04754_eq_value :
    recordGapCenter + 195218 = fullRecordGapValue04754 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04754_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04754 (fullRecordGapValue04754 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04754_not_prime : ¬(recordGapCenter + 195218).Prime := by
  rw [fullRecordGapTerm04754_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04754, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04754_fast_pow_mod_ne_one

def fullRecordGapValue04755 : Nat := fullRecordGapCenterValue + 195302

theorem fullRecordGapTerm04755_eq_value :
    recordGapCenter + 195302 = fullRecordGapValue04755 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04755_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04755 (fullRecordGapValue04755 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04755_not_prime : ¬(recordGapCenter + 195302).Prime := by
  rw [fullRecordGapTerm04755_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04755, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04755_fast_pow_mod_ne_one

def fullRecordGapValue04756 : Nat := fullRecordGapCenterValue + 195428

theorem fullRecordGapTerm04756_eq_value :
    recordGapCenter + 195428 = fullRecordGapValue04756 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04756_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04756 (fullRecordGapValue04756 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04756_not_prime : ¬(recordGapCenter + 195428).Prime := by
  rw [fullRecordGapTerm04756_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04756, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04756_fast_pow_mod_ne_one

def fullRecordGapValue04757 : Nat := fullRecordGapCenterValue + 195458

theorem fullRecordGapTerm04757_eq_value :
    recordGapCenter + 195458 = fullRecordGapValue04757 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04757_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04757 (fullRecordGapValue04757 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04757_not_prime : ¬(recordGapCenter + 195458).Prime := by
  rw [fullRecordGapTerm04757_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04757, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04757_fast_pow_mod_ne_one

def fullRecordGapValue04758 : Nat := fullRecordGapCenterValue + 195542

theorem fullRecordGapTerm04758_eq_value :
    recordGapCenter + 195542 = fullRecordGapValue04758 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04758_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04758 (fullRecordGapValue04758 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04758_not_prime : ¬(recordGapCenter + 195542).Prime := by
  rw [fullRecordGapTerm04758_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04758, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04758_fast_pow_mod_ne_one

def fullRecordGapValue04759 : Nat := fullRecordGapCenterValue + 196022

theorem fullRecordGapTerm04759_eq_value :
    recordGapCenter + 196022 = fullRecordGapValue04759 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04759_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04759 (fullRecordGapValue04759 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04759_not_prime : ¬(recordGapCenter + 196022).Prime := by
  rw [fullRecordGapTerm04759_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04759, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04759_fast_pow_mod_ne_one

def fullRecordGapValue04760 : Nat := fullRecordGapCenterValue + 196436

theorem fullRecordGapTerm04760_eq_value :
    recordGapCenter + 196436 = fullRecordGapValue04760 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04760_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04760 (fullRecordGapValue04760 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04760_not_prime : ¬(recordGapCenter + 196436).Prime := by
  rw [fullRecordGapTerm04760_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04760, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04760_fast_pow_mod_ne_one

def fullRecordGapValue04761 : Nat := fullRecordGapCenterValue + 196502

theorem fullRecordGapTerm04761_eq_value :
    recordGapCenter + 196502 = fullRecordGapValue04761 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04761_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04761 (fullRecordGapValue04761 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04761_not_prime : ¬(recordGapCenter + 196502).Prime := by
  rw [fullRecordGapTerm04761_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04761, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04761_fast_pow_mod_ne_one

def fullRecordGapValue04762 : Nat := fullRecordGapCenterValue + 196556

theorem fullRecordGapTerm04762_eq_value :
    recordGapCenter + 196556 = fullRecordGapValue04762 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04762_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04762 (fullRecordGapValue04762 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04762_not_prime : ¬(recordGapCenter + 196556).Prime := by
  rw [fullRecordGapTerm04762_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04762, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04762_fast_pow_mod_ne_one

def fullRecordGapValue04763 : Nat := fullRecordGapCenterValue + 196628

theorem fullRecordGapTerm04763_eq_value :
    recordGapCenter + 196628 = fullRecordGapValue04763 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04763_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04763 (fullRecordGapValue04763 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04763_not_prime : ¬(recordGapCenter + 196628).Prime := by
  rw [fullRecordGapTerm04763_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04763, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04763_fast_pow_mod_ne_one

def fullRecordGapValue04764 : Nat := fullRecordGapCenterValue + 196646

theorem fullRecordGapTerm04764_eq_value :
    recordGapCenter + 196646 = fullRecordGapValue04764 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04764_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04764 (fullRecordGapValue04764 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04764_not_prime : ¬(recordGapCenter + 196646).Prime := by
  rw [fullRecordGapTerm04764_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04764, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04764_fast_pow_mod_ne_one

def fullRecordGapValue04765 : Nat := fullRecordGapCenterValue + 196778

theorem fullRecordGapTerm04765_eq_value :
    recordGapCenter + 196778 = fullRecordGapValue04765 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04765_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04765 (fullRecordGapValue04765 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04765_not_prime : ¬(recordGapCenter + 196778).Prime := by
  rw [fullRecordGapTerm04765_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04765, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04765_fast_pow_mod_ne_one

def fullRecordGapValue04766 : Nat := fullRecordGapCenterValue + 196796

theorem fullRecordGapTerm04766_eq_value :
    recordGapCenter + 196796 = fullRecordGapValue04766 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04766_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04766 (fullRecordGapValue04766 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04766_not_prime : ¬(recordGapCenter + 196796).Prime := by
  rw [fullRecordGapTerm04766_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04766, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04766_fast_pow_mod_ne_one

def fullRecordGapValue04767 : Nat := fullRecordGapCenterValue + 196886

theorem fullRecordGapTerm04767_eq_value :
    recordGapCenter + 196886 = fullRecordGapValue04767 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04767_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04767 (fullRecordGapValue04767 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04767_not_prime : ¬(recordGapCenter + 196886).Prime := by
  rw [fullRecordGapTerm04767_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04767, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04767_fast_pow_mod_ne_one

def fullRecordGapValue04768 : Nat := fullRecordGapCenterValue + 196892

theorem fullRecordGapTerm04768_eq_value :
    recordGapCenter + 196892 = fullRecordGapValue04768 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04768_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04768 (fullRecordGapValue04768 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04768_not_prime : ¬(recordGapCenter + 196892).Prime := by
  rw [fullRecordGapTerm04768_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04768, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04768_fast_pow_mod_ne_one

def fullRecordGapValue04769 : Nat := fullRecordGapCenterValue + 196982

theorem fullRecordGapTerm04769_eq_value :
    recordGapCenter + 196982 = fullRecordGapValue04769 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04769_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04769 (fullRecordGapValue04769 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04769_not_prime : ¬(recordGapCenter + 196982).Prime := by
  rw [fullRecordGapTerm04769_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04769, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04769_fast_pow_mod_ne_one

def fullRecordGapValue04770 : Nat := fullRecordGapCenterValue + 197108

theorem fullRecordGapTerm04770_eq_value :
    recordGapCenter + 197108 = fullRecordGapValue04770 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04770_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04770 (fullRecordGapValue04770 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04770_not_prime : ¬(recordGapCenter + 197108).Prime := by
  rw [fullRecordGapTerm04770_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04770, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04770_fast_pow_mod_ne_one

def fullRecordGapValue04771 : Nat := fullRecordGapCenterValue + 197120

theorem fullRecordGapTerm04771_eq_value :
    recordGapCenter + 197120 = fullRecordGapValue04771 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04771_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04771 (fullRecordGapValue04771 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04771_not_prime : ¬(recordGapCenter + 197120).Prime := by
  rw [fullRecordGapTerm04771_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04771, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04771_fast_pow_mod_ne_one

def fullRecordGapValue04772 : Nat := fullRecordGapCenterValue + 197426

theorem fullRecordGapTerm04772_eq_value :
    recordGapCenter + 197426 = fullRecordGapValue04772 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04772_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04772 (fullRecordGapValue04772 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04772_not_prime : ¬(recordGapCenter + 197426).Prime := by
  rw [fullRecordGapTerm04772_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04772, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04772_fast_pow_mod_ne_one

def fullRecordGapValue04773 : Nat := fullRecordGapCenterValue + 197558

theorem fullRecordGapTerm04773_eq_value :
    recordGapCenter + 197558 = fullRecordGapValue04773 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04773_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04773 (fullRecordGapValue04773 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04773_not_prime : ¬(recordGapCenter + 197558).Prime := by
  rw [fullRecordGapTerm04773_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04773, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04773_fast_pow_mod_ne_one

def fullRecordGapValue04774 : Nat := fullRecordGapCenterValue + 197822

theorem fullRecordGapTerm04774_eq_value :
    recordGapCenter + 197822 = fullRecordGapValue04774 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04774_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04774 (fullRecordGapValue04774 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04774_not_prime : ¬(recordGapCenter + 197822).Prime := by
  rw [fullRecordGapTerm04774_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04774, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04774_fast_pow_mod_ne_one

def fullRecordGapValue04775 : Nat := fullRecordGapCenterValue + 197852

theorem fullRecordGapTerm04775_eq_value :
    recordGapCenter + 197852 = fullRecordGapValue04775 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04775_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04775 (fullRecordGapValue04775 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04775_not_prime : ¬(recordGapCenter + 197852).Prime := by
  rw [fullRecordGapTerm04775_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04775, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04775_fast_pow_mod_ne_one

def fullRecordGapValue04776 : Nat := fullRecordGapCenterValue + 197906

theorem fullRecordGapTerm04776_eq_value :
    recordGapCenter + 197906 = fullRecordGapValue04776 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04776_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04776 (fullRecordGapValue04776 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04776_not_prime : ¬(recordGapCenter + 197906).Prime := by
  rw [fullRecordGapTerm04776_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04776, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04776_fast_pow_mod_ne_one

def fullRecordGapValue04777 : Nat := fullRecordGapCenterValue + 198026

theorem fullRecordGapTerm04777_eq_value :
    recordGapCenter + 198026 = fullRecordGapValue04777 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04777_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04777 (fullRecordGapValue04777 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04777_not_prime : ¬(recordGapCenter + 198026).Prime := by
  rw [fullRecordGapTerm04777_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04777, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04777_fast_pow_mod_ne_one

def fullRecordGapValue04778 : Nat := fullRecordGapCenterValue + 198236

theorem fullRecordGapTerm04778_eq_value :
    recordGapCenter + 198236 = fullRecordGapValue04778 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04778_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04778 (fullRecordGapValue04778 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04778_not_prime : ¬(recordGapCenter + 198236).Prime := by
  rw [fullRecordGapTerm04778_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04778, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04778_fast_pow_mod_ne_one

def fullRecordGapValue04779 : Nat := fullRecordGapCenterValue + 198362

theorem fullRecordGapTerm04779_eq_value :
    recordGapCenter + 198362 = fullRecordGapValue04779 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04779_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04779 (fullRecordGapValue04779 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04779_not_prime : ¬(recordGapCenter + 198362).Prime := by
  rw [fullRecordGapTerm04779_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04779, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04779_fast_pow_mod_ne_one

def fullRecordGapValue04780 : Nat := fullRecordGapCenterValue + 198446

theorem fullRecordGapTerm04780_eq_value :
    recordGapCenter + 198446 = fullRecordGapValue04780 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04780_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04780 (fullRecordGapValue04780 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04780_not_prime : ¬(recordGapCenter + 198446).Prime := by
  rw [fullRecordGapTerm04780_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04780, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04780_fast_pow_mod_ne_one

def fullRecordGapValue04781 : Nat := fullRecordGapCenterValue + 198452

theorem fullRecordGapTerm04781_eq_value :
    recordGapCenter + 198452 = fullRecordGapValue04781 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04781_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04781 (fullRecordGapValue04781 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04781_not_prime : ¬(recordGapCenter + 198452).Prime := by
  rw [fullRecordGapTerm04781_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04781, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04781_fast_pow_mod_ne_one

def fullRecordGapValue04782 : Nat := fullRecordGapCenterValue + 198482

theorem fullRecordGapTerm04782_eq_value :
    recordGapCenter + 198482 = fullRecordGapValue04782 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04782_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04782 (fullRecordGapValue04782 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04782_not_prime : ¬(recordGapCenter + 198482).Prime := by
  rw [fullRecordGapTerm04782_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04782, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04782_fast_pow_mod_ne_one

def fullRecordGapValue04783 : Nat := fullRecordGapCenterValue + 198518

theorem fullRecordGapTerm04783_eq_value :
    recordGapCenter + 198518 = fullRecordGapValue04783 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04783_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04783 (fullRecordGapValue04783 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04783_not_prime : ¬(recordGapCenter + 198518).Prime := by
  rw [fullRecordGapTerm04783_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04783, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04783_fast_pow_mod_ne_one

def fullRecordGapValue04784 : Nat := fullRecordGapCenterValue + 198578

theorem fullRecordGapTerm04784_eq_value :
    recordGapCenter + 198578 = fullRecordGapValue04784 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04784_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04784 (fullRecordGapValue04784 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04784_not_prime : ¬(recordGapCenter + 198578).Prime := by
  rw [fullRecordGapTerm04784_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04784, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04784_fast_pow_mod_ne_one

def fullRecordGapValue04785 : Nat := fullRecordGapCenterValue + 198668

theorem fullRecordGapTerm04785_eq_value :
    recordGapCenter + 198668 = fullRecordGapValue04785 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04785_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04785 (fullRecordGapValue04785 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04785_not_prime : ¬(recordGapCenter + 198668).Prime := by
  rw [fullRecordGapTerm04785_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04785, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04785_fast_pow_mod_ne_one

def fullRecordGapValue04786 : Nat := fullRecordGapCenterValue + 198698

theorem fullRecordGapTerm04786_eq_value :
    recordGapCenter + 198698 = fullRecordGapValue04786 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04786_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04786 (fullRecordGapValue04786 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04786_not_prime : ¬(recordGapCenter + 198698).Prime := by
  rw [fullRecordGapTerm04786_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04786, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04786_fast_pow_mod_ne_one

def fullRecordGapValue04787 : Nat := fullRecordGapCenterValue + 198878

theorem fullRecordGapTerm04787_eq_value :
    recordGapCenter + 198878 = fullRecordGapValue04787 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04787_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04787 (fullRecordGapValue04787 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04787_not_prime : ¬(recordGapCenter + 198878).Prime := by
  rw [fullRecordGapTerm04787_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04787, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04787_fast_pow_mod_ne_one

def fullRecordGapValue04788 : Nat := fullRecordGapCenterValue + 198908

theorem fullRecordGapTerm04788_eq_value :
    recordGapCenter + 198908 = fullRecordGapValue04788 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04788_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04788 (fullRecordGapValue04788 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04788_not_prime : ¬(recordGapCenter + 198908).Prime := by
  rw [fullRecordGapTerm04788_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04788, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04788_fast_pow_mod_ne_one

def fullRecordGapValue04789 : Nat := fullRecordGapCenterValue + 199028

theorem fullRecordGapTerm04789_eq_value :
    recordGapCenter + 199028 = fullRecordGapValue04789 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04789_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04789 (fullRecordGapValue04789 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04789_not_prime : ¬(recordGapCenter + 199028).Prime := by
  rw [fullRecordGapTerm04789_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04789, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04789_fast_pow_mod_ne_one

def fullRecordGapValue04790 : Nat := fullRecordGapCenterValue + 199046

theorem fullRecordGapTerm04790_eq_value :
    recordGapCenter + 199046 = fullRecordGapValue04790 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04790_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04790 (fullRecordGapValue04790 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04790_not_prime : ¬(recordGapCenter + 199046).Prime := by
  rw [fullRecordGapTerm04790_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04790, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04790_fast_pow_mod_ne_one

def fullRecordGapValue04791 : Nat := fullRecordGapCenterValue + 199148

theorem fullRecordGapTerm04791_eq_value :
    recordGapCenter + 199148 = fullRecordGapValue04791 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04791_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04791 (fullRecordGapValue04791 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04791_not_prime : ¬(recordGapCenter + 199148).Prime := by
  rw [fullRecordGapTerm04791_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04791, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04791_fast_pow_mod_ne_one

def fullRecordGapValue04792 : Nat := fullRecordGapCenterValue + 199322

theorem fullRecordGapTerm04792_eq_value :
    recordGapCenter + 199322 = fullRecordGapValue04792 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04792_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04792 (fullRecordGapValue04792 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04792_not_prime : ¬(recordGapCenter + 199322).Prime := by
  rw [fullRecordGapTerm04792_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04792, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04792_fast_pow_mod_ne_one

def fullRecordGapValue04793 : Nat := fullRecordGapCenterValue + 199412

theorem fullRecordGapTerm04793_eq_value :
    recordGapCenter + 199412 = fullRecordGapValue04793 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04793_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04793 (fullRecordGapValue04793 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04793_not_prime : ¬(recordGapCenter + 199412).Prime := by
  rw [fullRecordGapTerm04793_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04793, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04793_fast_pow_mod_ne_one

def fullRecordGapValue04794 : Nat := fullRecordGapCenterValue + 199466

theorem fullRecordGapTerm04794_eq_value :
    recordGapCenter + 199466 = fullRecordGapValue04794 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04794_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04794 (fullRecordGapValue04794 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04794_not_prime : ¬(recordGapCenter + 199466).Prime := by
  rw [fullRecordGapTerm04794_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04794, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04794_fast_pow_mod_ne_one

def fullRecordGapValue04795 : Nat := fullRecordGapCenterValue + 199508

theorem fullRecordGapTerm04795_eq_value :
    recordGapCenter + 199508 = fullRecordGapValue04795 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04795_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04795 (fullRecordGapValue04795 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04795_not_prime : ¬(recordGapCenter + 199508).Prime := by
  rw [fullRecordGapTerm04795_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04795, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04795_fast_pow_mod_ne_one

def fullRecordGapValue04796 : Nat := fullRecordGapCenterValue + 199586

theorem fullRecordGapTerm04796_eq_value :
    recordGapCenter + 199586 = fullRecordGapValue04796 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04796_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04796 (fullRecordGapValue04796 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04796_not_prime : ¬(recordGapCenter + 199586).Prime := by
  rw [fullRecordGapTerm04796_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04796, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04796_fast_pow_mod_ne_one

def fullRecordGapValue04797 : Nat := fullRecordGapCenterValue + 199658

theorem fullRecordGapTerm04797_eq_value :
    recordGapCenter + 199658 = fullRecordGapValue04797 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04797_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04797 (fullRecordGapValue04797 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04797_not_prime : ¬(recordGapCenter + 199658).Prime := by
  rw [fullRecordGapTerm04797_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04797, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04797_fast_pow_mod_ne_one

def fullRecordGapValue04798 : Nat := fullRecordGapCenterValue + 199748

theorem fullRecordGapTerm04798_eq_value :
    recordGapCenter + 199748 = fullRecordGapValue04798 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04798_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04798 (fullRecordGapValue04798 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04798_not_prime : ¬(recordGapCenter + 199748).Prime := by
  rw [fullRecordGapTerm04798_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04798, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04798_fast_pow_mod_ne_one

def fullRecordGapValue04799 : Nat := fullRecordGapCenterValue + 200132

theorem fullRecordGapTerm04799_eq_value :
    recordGapCenter + 200132 = fullRecordGapValue04799 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04799_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04799 (fullRecordGapValue04799 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04799_not_prime : ¬(recordGapCenter + 200132).Prime := by
  rw [fullRecordGapTerm04799_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04799, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04799_fast_pow_mod_ne_one

def fullRecordGapValue04800 : Nat := fullRecordGapCenterValue + 200348

theorem fullRecordGapTerm04800_eq_value :
    recordGapCenter + 200348 = fullRecordGapValue04800 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04800_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04800 (fullRecordGapValue04800 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04800_not_prime : ¬(recordGapCenter + 200348).Prime := by
  rw [fullRecordGapTerm04800_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04800, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04800_fast_pow_mod_ne_one

def fullRecordGapValue04801 : Nat := fullRecordGapCenterValue + 200378

theorem fullRecordGapTerm04801_eq_value :
    recordGapCenter + 200378 = fullRecordGapValue04801 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04801_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04801 (fullRecordGapValue04801 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04801_not_prime : ¬(recordGapCenter + 200378).Prime := by
  rw [fullRecordGapTerm04801_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04801, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04801_fast_pow_mod_ne_one

def fullRecordGapValue04802 : Nat := fullRecordGapCenterValue + 200426

theorem fullRecordGapTerm04802_eq_value :
    recordGapCenter + 200426 = fullRecordGapValue04802 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04802_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04802 (fullRecordGapValue04802 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04802_not_prime : ¬(recordGapCenter + 200426).Prime := by
  rw [fullRecordGapTerm04802_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04802, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04802_fast_pow_mod_ne_one

def fullRecordGapValue04803 : Nat := fullRecordGapCenterValue + 200516

theorem fullRecordGapTerm04803_eq_value :
    recordGapCenter + 200516 = fullRecordGapValue04803 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04803_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04803 (fullRecordGapValue04803 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04803_not_prime : ¬(recordGapCenter + 200516).Prime := by
  rw [fullRecordGapTerm04803_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04803, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04803_fast_pow_mod_ne_one

def fullRecordGapValue04804 : Nat := fullRecordGapCenterValue + 200666

theorem fullRecordGapTerm04804_eq_value :
    recordGapCenter + 200666 = fullRecordGapValue04804 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04804_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04804 (fullRecordGapValue04804 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04804_not_prime : ¬(recordGapCenter + 200666).Prime := by
  rw [fullRecordGapTerm04804_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04804, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04804_fast_pow_mod_ne_one

def fullRecordGapValue04805 : Nat := fullRecordGapCenterValue + 200708

theorem fullRecordGapTerm04805_eq_value :
    recordGapCenter + 200708 = fullRecordGapValue04805 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04805_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04805 (fullRecordGapValue04805 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04805_not_prime : ¬(recordGapCenter + 200708).Prime := by
  rw [fullRecordGapTerm04805_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04805, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04805_fast_pow_mod_ne_one

def fullRecordGapValue04806 : Nat := fullRecordGapCenterValue + 200726

theorem fullRecordGapTerm04806_eq_value :
    recordGapCenter + 200726 = fullRecordGapValue04806 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04806_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04806 (fullRecordGapValue04806 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04806_not_prime : ¬(recordGapCenter + 200726).Prime := by
  rw [fullRecordGapTerm04806_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04806, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04806_fast_pow_mod_ne_one

def fullRecordGapValue04807 : Nat := fullRecordGapCenterValue + 200786

theorem fullRecordGapTerm04807_eq_value :
    recordGapCenter + 200786 = fullRecordGapValue04807 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04807_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04807 (fullRecordGapValue04807 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04807_not_prime : ¬(recordGapCenter + 200786).Prime := by
  rw [fullRecordGapTerm04807_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04807, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04807_fast_pow_mod_ne_one

def fullRecordGapValue04808 : Nat := fullRecordGapCenterValue + 200828

theorem fullRecordGapTerm04808_eq_value :
    recordGapCenter + 200828 = fullRecordGapValue04808 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04808_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04808 (fullRecordGapValue04808 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04808_not_prime : ¬(recordGapCenter + 200828).Prime := by
  rw [fullRecordGapTerm04808_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04808, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04808_fast_pow_mod_ne_one

def fullRecordGapValue04809 : Nat := fullRecordGapCenterValue + 200918

theorem fullRecordGapTerm04809_eq_value :
    recordGapCenter + 200918 = fullRecordGapValue04809 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04809_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04809 (fullRecordGapValue04809 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04809_not_prime : ¬(recordGapCenter + 200918).Prime := by
  rw [fullRecordGapTerm04809_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04809, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04809_fast_pow_mod_ne_one

def fullRecordGapValue04810 : Nat := fullRecordGapCenterValue + 201218

theorem fullRecordGapTerm04810_eq_value :
    recordGapCenter + 201218 = fullRecordGapValue04810 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04810_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04810 (fullRecordGapValue04810 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04810_not_prime : ¬(recordGapCenter + 201218).Prime := by
  rw [fullRecordGapTerm04810_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04810, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04810_fast_pow_mod_ne_one

def fullRecordGapValue04811 : Nat := fullRecordGapCenterValue + 201332

theorem fullRecordGapTerm04811_eq_value :
    recordGapCenter + 201332 = fullRecordGapValue04811 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04811_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04811 (fullRecordGapValue04811 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04811_not_prime : ¬(recordGapCenter + 201332).Prime := by
  rw [fullRecordGapTerm04811_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04811, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04811_fast_pow_mod_ne_one

def fullRecordGapValue04812 : Nat := fullRecordGapCenterValue + 201338

theorem fullRecordGapTerm04812_eq_value :
    recordGapCenter + 201338 = fullRecordGapValue04812 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04812_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04812 (fullRecordGapValue04812 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04812_not_prime : ¬(recordGapCenter + 201338).Prime := by
  rw [fullRecordGapTerm04812_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04812, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04812_fast_pow_mod_ne_one

def fullRecordGapValue04813 : Nat := fullRecordGapCenterValue + 201602

theorem fullRecordGapTerm04813_eq_value :
    recordGapCenter + 201602 = fullRecordGapValue04813 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04813_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04813 (fullRecordGapValue04813 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04813_not_prime : ¬(recordGapCenter + 201602).Prime := by
  rw [fullRecordGapTerm04813_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04813, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04813_fast_pow_mod_ne_one

def fullRecordGapValue04814 : Nat := fullRecordGapCenterValue + 201668

theorem fullRecordGapTerm04814_eq_value :
    recordGapCenter + 201668 = fullRecordGapValue04814 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04814_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04814 (fullRecordGapValue04814 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04814_not_prime : ¬(recordGapCenter + 201668).Prime := by
  rw [fullRecordGapTerm04814_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04814, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04814_fast_pow_mod_ne_one

def fullRecordGapValue04815 : Nat := fullRecordGapCenterValue + 201836

theorem fullRecordGapTerm04815_eq_value :
    recordGapCenter + 201836 = fullRecordGapValue04815 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04815_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04815 (fullRecordGapValue04815 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04815_not_prime : ¬(recordGapCenter + 201836).Prime := by
  rw [fullRecordGapTerm04815_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04815, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04815_fast_pow_mod_ne_one

def fullRecordGapValue04816 : Nat := fullRecordGapCenterValue + 202298

theorem fullRecordGapTerm04816_eq_value :
    recordGapCenter + 202298 = fullRecordGapValue04816 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04816_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04816 (fullRecordGapValue04816 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04816_not_prime : ¬(recordGapCenter + 202298).Prime := by
  rw [fullRecordGapTerm04816_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04816, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04816_fast_pow_mod_ne_one

def fullRecordGapValue04817 : Nat := fullRecordGapCenterValue + 202406

theorem fullRecordGapTerm04817_eq_value :
    recordGapCenter + 202406 = fullRecordGapValue04817 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04817_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04817 (fullRecordGapValue04817 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04817_not_prime : ¬(recordGapCenter + 202406).Prime := by
  rw [fullRecordGapTerm04817_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04817, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04817_fast_pow_mod_ne_one

def fullRecordGapValue04818 : Nat := fullRecordGapCenterValue + 202500

theorem fullRecordGapTerm04818_eq_value :
    recordGapCenter + 202500 = fullRecordGapValue04818 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04818_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04818 (fullRecordGapValue04818 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04818_not_prime : ¬(recordGapCenter + 202500).Prime := by
  rw [fullRecordGapTerm04818_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04818, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04818_fast_pow_mod_ne_one

def fullRecordGapValue04819 : Nat := fullRecordGapCenterValue + 202562

theorem fullRecordGapTerm04819_eq_value :
    recordGapCenter + 202562 = fullRecordGapValue04819 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04819_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04819 (fullRecordGapValue04819 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04819_not_prime : ¬(recordGapCenter + 202562).Prime := by
  rw [fullRecordGapTerm04819_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04819, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04819_fast_pow_mod_ne_one

def fullRecordGapValue04820 : Nat := fullRecordGapCenterValue + 202718

theorem fullRecordGapTerm04820_eq_value :
    recordGapCenter + 202718 = fullRecordGapValue04820 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04820_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04820 (fullRecordGapValue04820 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04820_not_prime : ¬(recordGapCenter + 202718).Prime := by
  rw [fullRecordGapTerm04820_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04820, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04820_fast_pow_mod_ne_one

def fullRecordGapValue04821 : Nat := fullRecordGapCenterValue + 202898

theorem fullRecordGapTerm04821_eq_value :
    recordGapCenter + 202898 = fullRecordGapValue04821 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04821_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04821 (fullRecordGapValue04821 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04821_not_prime : ¬(recordGapCenter + 202898).Prime := by
  rw [fullRecordGapTerm04821_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04821, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04821_fast_pow_mod_ne_one

def fullRecordGapValue04822 : Nat := fullRecordGapCenterValue + 203066

theorem fullRecordGapTerm04822_eq_value :
    recordGapCenter + 203066 = fullRecordGapValue04822 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04822_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04822 (fullRecordGapValue04822 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04822_not_prime : ¬(recordGapCenter + 203066).Prime := by
  rw [fullRecordGapTerm04822_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04822, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04822_fast_pow_mod_ne_one

def fullRecordGapValue04823 : Nat := fullRecordGapCenterValue + 203108

theorem fullRecordGapTerm04823_eq_value :
    recordGapCenter + 203108 = fullRecordGapValue04823 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04823_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04823 (fullRecordGapValue04823 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04823_not_prime : ¬(recordGapCenter + 203108).Prime := by
  rw [fullRecordGapTerm04823_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04823, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04823_fast_pow_mod_ne_one

def fullRecordGapValue04824 : Nat := fullRecordGapCenterValue + 203280

theorem fullRecordGapTerm04824_eq_value :
    recordGapCenter + 203280 = fullRecordGapValue04824 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04824_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04824 (fullRecordGapValue04824 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04824_not_prime : ¬(recordGapCenter + 203280).Prime := by
  rw [fullRecordGapTerm04824_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04824, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04824_fast_pow_mod_ne_one

def fullRecordGapValue04825 : Nat := fullRecordGapCenterValue + 203402

theorem fullRecordGapTerm04825_eq_value :
    recordGapCenter + 203402 = fullRecordGapValue04825 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04825_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04825 (fullRecordGapValue04825 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04825_not_prime : ¬(recordGapCenter + 203402).Prime := by
  rw [fullRecordGapTerm04825_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04825, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04825_fast_pow_mod_ne_one

def fullRecordGapValue04826 : Nat := fullRecordGapCenterValue + 203438

theorem fullRecordGapTerm04826_eq_value :
    recordGapCenter + 203438 = fullRecordGapValue04826 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04826_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04826 (fullRecordGapValue04826 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04826_not_prime : ¬(recordGapCenter + 203438).Prime := by
  rw [fullRecordGapTerm04826_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04826, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04826_fast_pow_mod_ne_one

def fullRecordGapValue04827 : Nat := fullRecordGapCenterValue + 203492

theorem fullRecordGapTerm04827_eq_value :
    recordGapCenter + 203492 = fullRecordGapValue04827 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04827_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04827 (fullRecordGapValue04827 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04827_not_prime : ¬(recordGapCenter + 203492).Prime := by
  rw [fullRecordGapTerm04827_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04827, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04827_fast_pow_mod_ne_one

def fullRecordGapValue04828 : Nat := fullRecordGapCenterValue + 203726

theorem fullRecordGapTerm04828_eq_value :
    recordGapCenter + 203726 = fullRecordGapValue04828 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04828_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04828 (fullRecordGapValue04828 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04828_not_prime : ¬(recordGapCenter + 203726).Prime := by
  rw [fullRecordGapTerm04828_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04828, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04828_fast_pow_mod_ne_one

def fullRecordGapValue04829 : Nat := fullRecordGapCenterValue + 203742

theorem fullRecordGapTerm04829_eq_value :
    recordGapCenter + 203742 = fullRecordGapValue04829 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04829_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04829 (fullRecordGapValue04829 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04829_not_prime : ¬(recordGapCenter + 203742).Prime := by
  rw [fullRecordGapTerm04829_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04829, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04829_fast_pow_mod_ne_one

def fullRecordGapValue04830 : Nat := fullRecordGapCenterValue + 203828

theorem fullRecordGapTerm04830_eq_value :
    recordGapCenter + 203828 = fullRecordGapValue04830 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04830_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04830 (fullRecordGapValue04830 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04830_not_prime : ¬(recordGapCenter + 203828).Prime := by
  rw [fullRecordGapTerm04830_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04830, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04830_fast_pow_mod_ne_one

def fullRecordGapValue04831 : Nat := fullRecordGapCenterValue + 203876

theorem fullRecordGapTerm04831_eq_value :
    recordGapCenter + 203876 = fullRecordGapValue04831 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04831_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04831 (fullRecordGapValue04831 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04831_not_prime : ¬(recordGapCenter + 203876).Prime := by
  rw [fullRecordGapTerm04831_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04831, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04831_fast_pow_mod_ne_one

def fullRecordGapValue04832 : Nat := fullRecordGapCenterValue + 204026

theorem fullRecordGapTerm04832_eq_value :
    recordGapCenter + 204026 = fullRecordGapValue04832 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04832_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04832 (fullRecordGapValue04832 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04832_not_prime : ¬(recordGapCenter + 204026).Prime := by
  rw [fullRecordGapTerm04832_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04832, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04832_fast_pow_mod_ne_one

def fullRecordGapValue04833 : Nat := fullRecordGapCenterValue + 204122

theorem fullRecordGapTerm04833_eq_value :
    recordGapCenter + 204122 = fullRecordGapValue04833 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04833_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04833 (fullRecordGapValue04833 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04833_not_prime : ¬(recordGapCenter + 204122).Prime := by
  rw [fullRecordGapTerm04833_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04833, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04833_fast_pow_mod_ne_one

def fullRecordGapValue04834 : Nat := fullRecordGapCenterValue + 204158

theorem fullRecordGapTerm04834_eq_value :
    recordGapCenter + 204158 = fullRecordGapValue04834 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04834_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04834 (fullRecordGapValue04834 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04834_not_prime : ¬(recordGapCenter + 204158).Prime := by
  rw [fullRecordGapTerm04834_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04834, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04834_fast_pow_mod_ne_one

def fullRecordGapValue04835 : Nat := fullRecordGapCenterValue + 204188

theorem fullRecordGapTerm04835_eq_value :
    recordGapCenter + 204188 = fullRecordGapValue04835 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04835_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04835 (fullRecordGapValue04835 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04835_not_prime : ¬(recordGapCenter + 204188).Prime := by
  rw [fullRecordGapTerm04835_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04835, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04835_fast_pow_mod_ne_one

def fullRecordGapValue04836 : Nat := fullRecordGapCenterValue + 204362

theorem fullRecordGapTerm04836_eq_value :
    recordGapCenter + 204362 = fullRecordGapValue04836 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04836_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04836 (fullRecordGapValue04836 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04836_not_prime : ¬(recordGapCenter + 204362).Prime := by
  rw [fullRecordGapTerm04836_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04836, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04836_fast_pow_mod_ne_one

def fullRecordGapValue04837 : Nat := fullRecordGapCenterValue + 204482

theorem fullRecordGapTerm04837_eq_value :
    recordGapCenter + 204482 = fullRecordGapValue04837 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04837_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04837 (fullRecordGapValue04837 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04837_not_prime : ¬(recordGapCenter + 204482).Prime := by
  rw [fullRecordGapTerm04837_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04837, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04837_fast_pow_mod_ne_one

def fullRecordGapValue04838 : Nat := fullRecordGapCenterValue + 204506

theorem fullRecordGapTerm04838_eq_value :
    recordGapCenter + 204506 = fullRecordGapValue04838 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04838_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04838 (fullRecordGapValue04838 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04838_not_prime : ¬(recordGapCenter + 204506).Prime := by
  rw [fullRecordGapTerm04838_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04838, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04838_fast_pow_mod_ne_one

def fullRecordGapValue04839 : Nat := fullRecordGapCenterValue + 204998

theorem fullRecordGapTerm04839_eq_value :
    recordGapCenter + 204998 = fullRecordGapValue04839 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04839_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04839 (fullRecordGapValue04839 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04839_not_prime : ¬(recordGapCenter + 204998).Prime := by
  rw [fullRecordGapTerm04839_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04839, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04839_fast_pow_mod_ne_one

def fullRecordGapValue04840 : Nat := fullRecordGapCenterValue + 205028

theorem fullRecordGapTerm04840_eq_value :
    recordGapCenter + 205028 = fullRecordGapValue04840 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04840_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04840 (fullRecordGapValue04840 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04840_not_prime : ¬(recordGapCenter + 205028).Prime := by
  rw [fullRecordGapTerm04840_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04840, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04840_fast_pow_mod_ne_one

def fullRecordGapValue04841 : Nat := fullRecordGapCenterValue + 205046

theorem fullRecordGapTerm04841_eq_value :
    recordGapCenter + 205046 = fullRecordGapValue04841 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04841_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04841 (fullRecordGapValue04841 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04841_not_prime : ¬(recordGapCenter + 205046).Prime := by
  rw [fullRecordGapTerm04841_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04841, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04841_fast_pow_mod_ne_one

def fullRecordGapValue04842 : Nat := fullRecordGapCenterValue + 205118

theorem fullRecordGapTerm04842_eq_value :
    recordGapCenter + 205118 = fullRecordGapValue04842 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04842_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04842 (fullRecordGapValue04842 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04842_not_prime : ¬(recordGapCenter + 205118).Prime := by
  rw [fullRecordGapTerm04842_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04842, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04842_fast_pow_mod_ne_one

def fullRecordGapValue04843 : Nat := fullRecordGapCenterValue + 205286

theorem fullRecordGapTerm04843_eq_value :
    recordGapCenter + 205286 = fullRecordGapValue04843 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04843_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04843 (fullRecordGapValue04843 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04843_not_prime : ¬(recordGapCenter + 205286).Prime := by
  rw [fullRecordGapTerm04843_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04843, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04843_fast_pow_mod_ne_one

def fullRecordGapValue04844 : Nat := fullRecordGapCenterValue + 205346

theorem fullRecordGapTerm04844_eq_value :
    recordGapCenter + 205346 = fullRecordGapValue04844 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04844_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04844 (fullRecordGapValue04844 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04844_not_prime : ¬(recordGapCenter + 205346).Prime := by
  rw [fullRecordGapTerm04844_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04844, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04844_fast_pow_mod_ne_one

def fullRecordGapValue04845 : Nat := fullRecordGapCenterValue + 205538

theorem fullRecordGapTerm04845_eq_value :
    recordGapCenter + 205538 = fullRecordGapValue04845 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04845_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04845 (fullRecordGapValue04845 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04845_not_prime : ¬(recordGapCenter + 205538).Prime := by
  rw [fullRecordGapTerm04845_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04845, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04845_fast_pow_mod_ne_one

def fullRecordGapValue04846 : Nat := fullRecordGapCenterValue + 205622

theorem fullRecordGapTerm04846_eq_value :
    recordGapCenter + 205622 = fullRecordGapValue04846 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04846_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04846 (fullRecordGapValue04846 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04846_not_prime : ¬(recordGapCenter + 205622).Prime := by
  rw [fullRecordGapTerm04846_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04846, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04846_fast_pow_mod_ne_one

def fullRecordGapValue04847 : Nat := fullRecordGapCenterValue + 205628

theorem fullRecordGapTerm04847_eq_value :
    recordGapCenter + 205628 = fullRecordGapValue04847 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04847_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04847 (fullRecordGapValue04847 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04847_not_prime : ¬(recordGapCenter + 205628).Prime := by
  rw [fullRecordGapTerm04847_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04847, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04847_fast_pow_mod_ne_one

def fullRecordGapValue04848 : Nat := fullRecordGapCenterValue + 205658

theorem fullRecordGapTerm04848_eq_value :
    recordGapCenter + 205658 = fullRecordGapValue04848 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04848_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04848 (fullRecordGapValue04848 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04848_not_prime : ¬(recordGapCenter + 205658).Prime := by
  rw [fullRecordGapTerm04848_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04848, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04848_fast_pow_mod_ne_one

def fullRecordGapValue04849 : Nat := fullRecordGapCenterValue + 205682

theorem fullRecordGapTerm04849_eq_value :
    recordGapCenter + 205682 = fullRecordGapValue04849 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04849_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04849 (fullRecordGapValue04849 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04849_not_prime : ¬(recordGapCenter + 205682).Prime := by
  rw [fullRecordGapTerm04849_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04849, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04849_fast_pow_mod_ne_one

def fullRecordGapValue04850 : Nat := fullRecordGapCenterValue + 206252

theorem fullRecordGapTerm04850_eq_value :
    recordGapCenter + 206252 = fullRecordGapValue04850 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04850_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04850 (fullRecordGapValue04850 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04850_not_prime : ¬(recordGapCenter + 206252).Prime := by
  rw [fullRecordGapTerm04850_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04850, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04850_fast_pow_mod_ne_one

def fullRecordGapValue04851 : Nat := fullRecordGapCenterValue + 206372

theorem fullRecordGapTerm04851_eq_value :
    recordGapCenter + 206372 = fullRecordGapValue04851 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04851_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04851 (fullRecordGapValue04851 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04851_not_prime : ¬(recordGapCenter + 206372).Prime := by
  rw [fullRecordGapTerm04851_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04851, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04851_fast_pow_mod_ne_one

def fullRecordGapValue04852 : Nat := fullRecordGapCenterValue + 206582

theorem fullRecordGapTerm04852_eq_value :
    recordGapCenter + 206582 = fullRecordGapValue04852 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04852_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04852 (fullRecordGapValue04852 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04852_not_prime : ¬(recordGapCenter + 206582).Prime := by
  rw [fullRecordGapTerm04852_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04852, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04852_fast_pow_mod_ne_one

def fullRecordGapValue04853 : Nat := fullRecordGapCenterValue + 206636

theorem fullRecordGapTerm04853_eq_value :
    recordGapCenter + 206636 = fullRecordGapValue04853 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04853_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04853 (fullRecordGapValue04853 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04853_not_prime : ¬(recordGapCenter + 206636).Prime := by
  rw [fullRecordGapTerm04853_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04853, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04853_fast_pow_mod_ne_one

def fullRecordGapValue04854 : Nat := fullRecordGapCenterValue + 206666

theorem fullRecordGapTerm04854_eq_value :
    recordGapCenter + 206666 = fullRecordGapValue04854 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04854_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04854 (fullRecordGapValue04854 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04854_not_prime : ¬(recordGapCenter + 206666).Prime := by
  rw [fullRecordGapTerm04854_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04854, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04854_fast_pow_mod_ne_one

def fullRecordGapValue04855 : Nat := fullRecordGapCenterValue + 206798

theorem fullRecordGapTerm04855_eq_value :
    recordGapCenter + 206798 = fullRecordGapValue04855 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04855_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04855 (fullRecordGapValue04855 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04855_not_prime : ¬(recordGapCenter + 206798).Prime := by
  rw [fullRecordGapTerm04855_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04855, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04855_fast_pow_mod_ne_one

def fullRecordGapValue04856 : Nat := fullRecordGapCenterValue + 206846

theorem fullRecordGapTerm04856_eq_value :
    recordGapCenter + 206846 = fullRecordGapValue04856 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04856_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04856 (fullRecordGapValue04856 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04856_not_prime : ¬(recordGapCenter + 206846).Prime := by
  rw [fullRecordGapTerm04856_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04856, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04856_fast_pow_mod_ne_one

def fullRecordGapValue04857 : Nat := fullRecordGapCenterValue + 206942

theorem fullRecordGapTerm04857_eq_value :
    recordGapCenter + 206942 = fullRecordGapValue04857 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04857_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04857 (fullRecordGapValue04857 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04857_not_prime : ¬(recordGapCenter + 206942).Prime := by
  rw [fullRecordGapTerm04857_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04857, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04857_fast_pow_mod_ne_one

def fullRecordGapValue04858 : Nat := fullRecordGapCenterValue + 207068

theorem fullRecordGapTerm04858_eq_value :
    recordGapCenter + 207068 = fullRecordGapValue04858 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04858_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04858 (fullRecordGapValue04858 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04858_not_prime : ¬(recordGapCenter + 207068).Prime := by
  rw [fullRecordGapTerm04858_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04858, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04858_fast_pow_mod_ne_one

def fullRecordGapValue04859 : Nat := fullRecordGapCenterValue + 207182

theorem fullRecordGapTerm04859_eq_value :
    recordGapCenter + 207182 = fullRecordGapValue04859 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04859_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04859 (fullRecordGapValue04859 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04859_not_prime : ¬(recordGapCenter + 207182).Prime := by
  rw [fullRecordGapTerm04859_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04859, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04859_fast_pow_mod_ne_one

def fullRecordGapValue04860 : Nat := fullRecordGapCenterValue + 207212

theorem fullRecordGapTerm04860_eq_value :
    recordGapCenter + 207212 = fullRecordGapValue04860 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04860_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04860 (fullRecordGapValue04860 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04860_not_prime : ¬(recordGapCenter + 207212).Prime := by
  rw [fullRecordGapTerm04860_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04860, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04860_fast_pow_mod_ne_one

def fullRecordGapValue04861 : Nat := fullRecordGapCenterValue + 207338

theorem fullRecordGapTerm04861_eq_value :
    recordGapCenter + 207338 = fullRecordGapValue04861 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04861_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04861 (fullRecordGapValue04861 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04861_not_prime : ¬(recordGapCenter + 207338).Prime := by
  rw [fullRecordGapTerm04861_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04861, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04861_fast_pow_mod_ne_one

def fullRecordGapValue04862 : Nat := fullRecordGapCenterValue + 207362

theorem fullRecordGapTerm04862_eq_value :
    recordGapCenter + 207362 = fullRecordGapValue04862 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04862_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04862 (fullRecordGapValue04862 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04862_not_prime : ¬(recordGapCenter + 207362).Prime := by
  rw [fullRecordGapTerm04862_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04862, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04862_fast_pow_mod_ne_one

def fullRecordGapValue04863 : Nat := fullRecordGapCenterValue + 207572

theorem fullRecordGapTerm04863_eq_value :
    recordGapCenter + 207572 = fullRecordGapValue04863 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04863_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04863 (fullRecordGapValue04863 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04863_not_prime : ¬(recordGapCenter + 207572).Prime := by
  rw [fullRecordGapTerm04863_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04863, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04863_fast_pow_mod_ne_one

def fullRecordGapValue04864 : Nat := fullRecordGapCenterValue + 207926

theorem fullRecordGapTerm04864_eq_value :
    recordGapCenter + 207926 = fullRecordGapValue04864 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral04864_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue04864 (fullRecordGapValue04864 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm04864_not_prime : ¬(recordGapCenter + 207926).Prime := by
  rw [fullRecordGapTerm04864_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue04864, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral04864_fast_pow_mod_ne_one

end PrimeFactorUnimodality
