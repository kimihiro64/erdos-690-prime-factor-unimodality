import PrimeFactorUnimodality.Helpers.Arithmetic.FastPowMod
import PrimeFactorUnimodality.Proof.LargeRange.Generated.FullRecordGapCenter

set_option autoImplicit false
set_option maxRecDepth 10000000
set_option linter.style.longLine false

namespace PrimeFactorUnimodality

def fullRecordGapValue01537 : Nat := fullRecordGapCenterValue - 333714

theorem fullRecordGapTerm01537_eq_value :
    recordGapCenter - 333714 = fullRecordGapValue01537 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01537_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01537 (fullRecordGapValue01537 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01537_not_prime : ¬(recordGapCenter - 333714).Prime := by
  rw [fullRecordGapTerm01537_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01537, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01537_fast_pow_mod_ne_one

def fullRecordGapValue01538 : Nat := fullRecordGapCenterValue - 333694

theorem fullRecordGapTerm01538_eq_value :
    recordGapCenter - 333694 = fullRecordGapValue01538 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01538_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01538 (fullRecordGapValue01538 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01538_not_prime : ¬(recordGapCenter - 333694).Prime := by
  rw [fullRecordGapTerm01538_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01538, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01538_fast_pow_mod_ne_one

def fullRecordGapValue01539 : Nat := fullRecordGapCenterValue - 333682

theorem fullRecordGapTerm01539_eq_value :
    recordGapCenter - 333682 = fullRecordGapValue01539 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01539_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01539 (fullRecordGapValue01539 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01539_not_prime : ¬(recordGapCenter - 333682).Prime := by
  rw [fullRecordGapTerm01539_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01539, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01539_fast_pow_mod_ne_one

def fullRecordGapValue01540 : Nat := fullRecordGapCenterValue - 333618

theorem fullRecordGapTerm01540_eq_value :
    recordGapCenter - 333618 = fullRecordGapValue01540 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01540_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01540 (fullRecordGapValue01540 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01540_not_prime : ¬(recordGapCenter - 333618).Prime := by
  rw [fullRecordGapTerm01540_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01540, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01540_fast_pow_mod_ne_one

def fullRecordGapValue01541 : Nat := fullRecordGapCenterValue - 333604

theorem fullRecordGapTerm01541_eq_value :
    recordGapCenter - 333604 = fullRecordGapValue01541 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01541_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01541 (fullRecordGapValue01541 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01541_not_prime : ¬(recordGapCenter - 333604).Prime := by
  rw [fullRecordGapTerm01541_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01541, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01541_fast_pow_mod_ne_one

def fullRecordGapValue01542 : Nat := fullRecordGapCenterValue - 333478

theorem fullRecordGapTerm01542_eq_value :
    recordGapCenter - 333478 = fullRecordGapValue01542 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01542_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01542 (fullRecordGapValue01542 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01542_not_prime : ¬(recordGapCenter - 333478).Prime := by
  rw [fullRecordGapTerm01542_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01542, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01542_fast_pow_mod_ne_one

def fullRecordGapValue01543 : Nat := fullRecordGapCenterValue - 333364

theorem fullRecordGapTerm01543_eq_value :
    recordGapCenter - 333364 = fullRecordGapValue01543 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01543_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01543 (fullRecordGapValue01543 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01543_not_prime : ¬(recordGapCenter - 333364).Prime := by
  rw [fullRecordGapTerm01543_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01543, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01543_fast_pow_mod_ne_one

def fullRecordGapValue01544 : Nat := fullRecordGapCenterValue - 333262

theorem fullRecordGapTerm01544_eq_value :
    recordGapCenter - 333262 = fullRecordGapValue01544 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01544_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01544 (fullRecordGapValue01544 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01544_not_prime : ¬(recordGapCenter - 333262).Prime := by
  rw [fullRecordGapTerm01544_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01544, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01544_fast_pow_mod_ne_one

def fullRecordGapValue01545 : Nat := fullRecordGapCenterValue - 333202

theorem fullRecordGapTerm01545_eq_value :
    recordGapCenter - 333202 = fullRecordGapValue01545 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01545_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01545 (fullRecordGapValue01545 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01545_not_prime : ¬(recordGapCenter - 333202).Prime := by
  rw [fullRecordGapTerm01545_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01545, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01545_fast_pow_mod_ne_one

def fullRecordGapValue01546 : Nat := fullRecordGapCenterValue - 333028

theorem fullRecordGapTerm01546_eq_value :
    recordGapCenter - 333028 = fullRecordGapValue01546 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01546_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01546 (fullRecordGapValue01546 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01546_not_prime : ¬(recordGapCenter - 333028).Prime := by
  rw [fullRecordGapTerm01546_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01546, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01546_fast_pow_mod_ne_one

def fullRecordGapValue01547 : Nat := fullRecordGapCenterValue - 332922

theorem fullRecordGapTerm01547_eq_value :
    recordGapCenter - 332922 = fullRecordGapValue01547 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01547_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01547 (fullRecordGapValue01547 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01547_not_prime : ¬(recordGapCenter - 332922).Prime := by
  rw [fullRecordGapTerm01547_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01547, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01547_fast_pow_mod_ne_one

def fullRecordGapValue01548 : Nat := fullRecordGapCenterValue - 332884

theorem fullRecordGapTerm01548_eq_value :
    recordGapCenter - 332884 = fullRecordGapValue01548 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01548_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01548 (fullRecordGapValue01548 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01548_not_prime : ¬(recordGapCenter - 332884).Prime := by
  rw [fullRecordGapTerm01548_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01548, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01548_fast_pow_mod_ne_one

def fullRecordGapValue01549 : Nat := fullRecordGapCenterValue - 332814

theorem fullRecordGapTerm01549_eq_value :
    recordGapCenter - 332814 = fullRecordGapValue01549 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01549_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01549 (fullRecordGapValue01549 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01549_not_prime : ¬(recordGapCenter - 332814).Prime := by
  rw [fullRecordGapTerm01549_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01549, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01549_fast_pow_mod_ne_one

def fullRecordGapValue01550 : Nat := fullRecordGapCenterValue - 332742

theorem fullRecordGapTerm01550_eq_value :
    recordGapCenter - 332742 = fullRecordGapValue01550 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01550_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01550 (fullRecordGapValue01550 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01550_not_prime : ¬(recordGapCenter - 332742).Prime := by
  rw [fullRecordGapTerm01550_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01550, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01550_fast_pow_mod_ne_one

def fullRecordGapValue01551 : Nat := fullRecordGapCenterValue - 332394

theorem fullRecordGapTerm01551_eq_value :
    recordGapCenter - 332394 = fullRecordGapValue01551 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01551_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01551 (fullRecordGapValue01551 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01551_not_prime : ¬(recordGapCenter - 332394).Prime := by
  rw [fullRecordGapTerm01551_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01551, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01551_fast_pow_mod_ne_one

def fullRecordGapValue01552 : Nat := fullRecordGapCenterValue - 332058

theorem fullRecordGapTerm01552_eq_value :
    recordGapCenter - 332058 = fullRecordGapValue01552 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01552_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01552 (fullRecordGapValue01552 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01552_not_prime : ¬(recordGapCenter - 332058).Prime := by
  rw [fullRecordGapTerm01552_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01552, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01552_fast_pow_mod_ne_one

def fullRecordGapValue01553 : Nat := fullRecordGapCenterValue - 331924

theorem fullRecordGapTerm01553_eq_value :
    recordGapCenter - 331924 = fullRecordGapValue01553 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01553_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01553 (fullRecordGapValue01553 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01553_not_prime : ¬(recordGapCenter - 331924).Prime := by
  rw [fullRecordGapTerm01553_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01553, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01553_fast_pow_mod_ne_one

def fullRecordGapValue01554 : Nat := fullRecordGapCenterValue - 331774

theorem fullRecordGapTerm01554_eq_value :
    recordGapCenter - 331774 = fullRecordGapValue01554 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01554_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01554 (fullRecordGapValue01554 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01554_not_prime : ¬(recordGapCenter - 331774).Prime := by
  rw [fullRecordGapTerm01554_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01554, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01554_fast_pow_mod_ne_one

def fullRecordGapValue01555 : Nat := fullRecordGapCenterValue - 331714

theorem fullRecordGapTerm01555_eq_value :
    recordGapCenter - 331714 = fullRecordGapValue01555 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01555_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01555 (fullRecordGapValue01555 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01555_not_prime : ¬(recordGapCenter - 331714).Prime := by
  rw [fullRecordGapTerm01555_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01555, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01555_fast_pow_mod_ne_one

def fullRecordGapValue01556 : Nat := fullRecordGapCenterValue - 331564

theorem fullRecordGapTerm01556_eq_value :
    recordGapCenter - 331564 = fullRecordGapValue01556 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01556_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01556 (fullRecordGapValue01556 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01556_not_prime : ¬(recordGapCenter - 331564).Prime := by
  rw [fullRecordGapTerm01556_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01556, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01556_fast_pow_mod_ne_one

def fullRecordGapValue01557 : Nat := fullRecordGapCenterValue - 331494

theorem fullRecordGapTerm01557_eq_value :
    recordGapCenter - 331494 = fullRecordGapValue01557 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01557_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01557 (fullRecordGapValue01557 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01557_not_prime : ¬(recordGapCenter - 331494).Prime := by
  rw [fullRecordGapTerm01557_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01557, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01557_fast_pow_mod_ne_one

def fullRecordGapValue01558 : Nat := fullRecordGapCenterValue - 331438

theorem fullRecordGapTerm01558_eq_value :
    recordGapCenter - 331438 = fullRecordGapValue01558 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01558_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01558 (fullRecordGapValue01558 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01558_not_prime : ¬(recordGapCenter - 331438).Prime := by
  rw [fullRecordGapTerm01558_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01558, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01558_fast_pow_mod_ne_one

def fullRecordGapValue01559 : Nat := fullRecordGapCenterValue - 331252

theorem fullRecordGapTerm01559_eq_value :
    recordGapCenter - 331252 = fullRecordGapValue01559 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01559_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01559 (fullRecordGapValue01559 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01559_not_prime : ¬(recordGapCenter - 331252).Prime := by
  rw [fullRecordGapTerm01559_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01559, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01559_fast_pow_mod_ne_one

def fullRecordGapValue01560 : Nat := fullRecordGapCenterValue - 331242

theorem fullRecordGapTerm01560_eq_value :
    recordGapCenter - 331242 = fullRecordGapValue01560 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01560_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01560 (fullRecordGapValue01560 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01560_not_prime : ¬(recordGapCenter - 331242).Prime := by
  rw [fullRecordGapTerm01560_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01560, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01560_fast_pow_mod_ne_one

def fullRecordGapValue01561 : Nat := fullRecordGapCenterValue - 331222

theorem fullRecordGapTerm01561_eq_value :
    recordGapCenter - 331222 = fullRecordGapValue01561 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01561_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01561 (fullRecordGapValue01561 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01561_not_prime : ¬(recordGapCenter - 331222).Prime := by
  rw [fullRecordGapTerm01561_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01561, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01561_fast_pow_mod_ne_one

def fullRecordGapValue01562 : Nat := fullRecordGapCenterValue - 331174

theorem fullRecordGapTerm01562_eq_value :
    recordGapCenter - 331174 = fullRecordGapValue01562 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01562_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01562 (fullRecordGapValue01562 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01562_not_prime : ¬(recordGapCenter - 331174).Prime := by
  rw [fullRecordGapTerm01562_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01562, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01562_fast_pow_mod_ne_one

def fullRecordGapValue01563 : Nat := fullRecordGapCenterValue - 331138

theorem fullRecordGapTerm01563_eq_value :
    recordGapCenter - 331138 = fullRecordGapValue01563 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01563_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01563 (fullRecordGapValue01563 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01563_not_prime : ¬(recordGapCenter - 331138).Prime := by
  rw [fullRecordGapTerm01563_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01563, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01563_fast_pow_mod_ne_one

def fullRecordGapValue01564 : Nat := fullRecordGapCenterValue - 331102

theorem fullRecordGapTerm01564_eq_value :
    recordGapCenter - 331102 = fullRecordGapValue01564 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01564_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01564 (fullRecordGapValue01564 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01564_not_prime : ¬(recordGapCenter - 331102).Prime := by
  rw [fullRecordGapTerm01564_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01564, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01564_fast_pow_mod_ne_one

def fullRecordGapValue01565 : Nat := fullRecordGapCenterValue - 331054

theorem fullRecordGapTerm01565_eq_value :
    recordGapCenter - 331054 = fullRecordGapValue01565 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01565_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01565 (fullRecordGapValue01565 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01565_not_prime : ¬(recordGapCenter - 331054).Prime := by
  rw [fullRecordGapTerm01565_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01565, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01565_fast_pow_mod_ne_one

def fullRecordGapValue01566 : Nat := fullRecordGapCenterValue - 330978

theorem fullRecordGapTerm01566_eq_value :
    recordGapCenter - 330978 = fullRecordGapValue01566 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01566_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01566 (fullRecordGapValue01566 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01566_not_prime : ¬(recordGapCenter - 330978).Prime := by
  rw [fullRecordGapTerm01566_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01566, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01566_fast_pow_mod_ne_one

def fullRecordGapValue01567 : Nat := fullRecordGapCenterValue - 330762

theorem fullRecordGapTerm01567_eq_value :
    recordGapCenter - 330762 = fullRecordGapValue01567 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01567_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01567 (fullRecordGapValue01567 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01567_not_prime : ¬(recordGapCenter - 330762).Prime := by
  rw [fullRecordGapTerm01567_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01567, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01567_fast_pow_mod_ne_one

def fullRecordGapValue01568 : Nat := fullRecordGapCenterValue - 330750

theorem fullRecordGapTerm01568_eq_value :
    recordGapCenter - 330750 = fullRecordGapValue01568 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01568_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01568 (fullRecordGapValue01568 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01568_not_prime : ¬(recordGapCenter - 330750).Prime := by
  rw [fullRecordGapTerm01568_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01568, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01568_fast_pow_mod_ne_one

def fullRecordGapValue01569 : Nat := fullRecordGapCenterValue - 330628

theorem fullRecordGapTerm01569_eq_value :
    recordGapCenter - 330628 = fullRecordGapValue01569 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01569_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01569 (fullRecordGapValue01569 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01569_not_prime : ¬(recordGapCenter - 330628).Prime := by
  rw [fullRecordGapTerm01569_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01569, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01569_fast_pow_mod_ne_one

def fullRecordGapValue01570 : Nat := fullRecordGapCenterValue - 330364

theorem fullRecordGapTerm01570_eq_value :
    recordGapCenter - 330364 = fullRecordGapValue01570 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01570_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01570 (fullRecordGapValue01570 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01570_not_prime : ¬(recordGapCenter - 330364).Prime := by
  rw [fullRecordGapTerm01570_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01570, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01570_fast_pow_mod_ne_one

def fullRecordGapValue01571 : Nat := fullRecordGapCenterValue - 330178

theorem fullRecordGapTerm01571_eq_value :
    recordGapCenter - 330178 = fullRecordGapValue01571 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01571_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01571 (fullRecordGapValue01571 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01571_not_prime : ¬(recordGapCenter - 330178).Prime := by
  rw [fullRecordGapTerm01571_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01571, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01571_fast_pow_mod_ne_one

def fullRecordGapValue01572 : Nat := fullRecordGapCenterValue - 330082

theorem fullRecordGapTerm01572_eq_value :
    recordGapCenter - 330082 = fullRecordGapValue01572 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01572_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01572 (fullRecordGapValue01572 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01572_not_prime : ¬(recordGapCenter - 330082).Prime := by
  rw [fullRecordGapTerm01572_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01572, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01572_fast_pow_mod_ne_one

def fullRecordGapValue01573 : Nat := fullRecordGapCenterValue - 330028

theorem fullRecordGapTerm01573_eq_value :
    recordGapCenter - 330028 = fullRecordGapValue01573 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01573_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01573 (fullRecordGapValue01573 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01573_not_prime : ¬(recordGapCenter - 330028).Prime := by
  rw [fullRecordGapTerm01573_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01573, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01573_fast_pow_mod_ne_one

def fullRecordGapValue01574 : Nat := fullRecordGapCenterValue - 330000

theorem fullRecordGapTerm01574_eq_value :
    recordGapCenter - 330000 = fullRecordGapValue01574 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01574_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01574 (fullRecordGapValue01574 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01574_not_prime : ¬(recordGapCenter - 330000).Prime := by
  rw [fullRecordGapTerm01574_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01574, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01574_fast_pow_mod_ne_one

def fullRecordGapValue01575 : Nat := fullRecordGapCenterValue - 329898

theorem fullRecordGapTerm01575_eq_value :
    recordGapCenter - 329898 = fullRecordGapValue01575 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01575_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01575 (fullRecordGapValue01575 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01575_not_prime : ¬(recordGapCenter - 329898).Prime := by
  rw [fullRecordGapTerm01575_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01575, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01575_fast_pow_mod_ne_one

def fullRecordGapValue01576 : Nat := fullRecordGapCenterValue - 329838

theorem fullRecordGapTerm01576_eq_value :
    recordGapCenter - 329838 = fullRecordGapValue01576 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01576_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01576 (fullRecordGapValue01576 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01576_not_prime : ¬(recordGapCenter - 329838).Prime := by
  rw [fullRecordGapTerm01576_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01576, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01576_fast_pow_mod_ne_one

def fullRecordGapValue01577 : Nat := fullRecordGapCenterValue - 329578

theorem fullRecordGapTerm01577_eq_value :
    recordGapCenter - 329578 = fullRecordGapValue01577 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01577_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01577 (fullRecordGapValue01577 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01577_not_prime : ¬(recordGapCenter - 329578).Prime := by
  rw [fullRecordGapTerm01577_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01577, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01577_fast_pow_mod_ne_one

def fullRecordGapValue01578 : Nat := fullRecordGapCenterValue - 329572

theorem fullRecordGapTerm01578_eq_value :
    recordGapCenter - 329572 = fullRecordGapValue01578 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01578_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01578 (fullRecordGapValue01578 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01578_not_prime : ¬(recordGapCenter - 329572).Prime := by
  rw [fullRecordGapTerm01578_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01578, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01578_fast_pow_mod_ne_one

def fullRecordGapValue01579 : Nat := fullRecordGapCenterValue - 329502

theorem fullRecordGapTerm01579_eq_value :
    recordGapCenter - 329502 = fullRecordGapValue01579 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01579_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01579 (fullRecordGapValue01579 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01579_not_prime : ¬(recordGapCenter - 329502).Prime := by
  rw [fullRecordGapTerm01579_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01579, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01579_fast_pow_mod_ne_one

def fullRecordGapValue01580 : Nat := fullRecordGapCenterValue - 329404

theorem fullRecordGapTerm01580_eq_value :
    recordGapCenter - 329404 = fullRecordGapValue01580 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01580_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01580 (fullRecordGapValue01580 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01580_not_prime : ¬(recordGapCenter - 329404).Prime := by
  rw [fullRecordGapTerm01580_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01580, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01580_fast_pow_mod_ne_one

def fullRecordGapValue01581 : Nat := fullRecordGapCenterValue - 329280

theorem fullRecordGapTerm01581_eq_value :
    recordGapCenter - 329280 = fullRecordGapValue01581 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01581_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01581 (fullRecordGapValue01581 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01581_not_prime : ¬(recordGapCenter - 329280).Prime := by
  rw [fullRecordGapTerm01581_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01581, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01581_fast_pow_mod_ne_one

def fullRecordGapValue01582 : Nat := fullRecordGapCenterValue - 329214

theorem fullRecordGapTerm01582_eq_value :
    recordGapCenter - 329214 = fullRecordGapValue01582 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01582_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01582 (fullRecordGapValue01582 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01582_not_prime : ¬(recordGapCenter - 329214).Prime := by
  rw [fullRecordGapTerm01582_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01582, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01582_fast_pow_mod_ne_one

def fullRecordGapValue01583 : Nat := fullRecordGapCenterValue - 329068

theorem fullRecordGapTerm01583_eq_value :
    recordGapCenter - 329068 = fullRecordGapValue01583 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01583_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01583 (fullRecordGapValue01583 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01583_not_prime : ¬(recordGapCenter - 329068).Prime := by
  rw [fullRecordGapTerm01583_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01583, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01583_fast_pow_mod_ne_one

def fullRecordGapValue01584 : Nat := fullRecordGapCenterValue - 329044

theorem fullRecordGapTerm01584_eq_value :
    recordGapCenter - 329044 = fullRecordGapValue01584 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01584_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01584 (fullRecordGapValue01584 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01584_not_prime : ¬(recordGapCenter - 329044).Prime := by
  rw [fullRecordGapTerm01584_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01584, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01584_fast_pow_mod_ne_one

def fullRecordGapValue01585 : Nat := fullRecordGapCenterValue - 328954

theorem fullRecordGapTerm01585_eq_value :
    recordGapCenter - 328954 = fullRecordGapValue01585 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01585_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01585 (fullRecordGapValue01585 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01585_not_prime : ¬(recordGapCenter - 328954).Prime := by
  rw [fullRecordGapTerm01585_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01585, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01585_fast_pow_mod_ne_one

def fullRecordGapValue01586 : Nat := fullRecordGapCenterValue - 328894

theorem fullRecordGapTerm01586_eq_value :
    recordGapCenter - 328894 = fullRecordGapValue01586 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01586_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01586 (fullRecordGapValue01586 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01586_not_prime : ¬(recordGapCenter - 328894).Prime := by
  rw [fullRecordGapTerm01586_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01586, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01586_fast_pow_mod_ne_one

def fullRecordGapValue01587 : Nat := fullRecordGapCenterValue - 328858

theorem fullRecordGapTerm01587_eq_value :
    recordGapCenter - 328858 = fullRecordGapValue01587 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01587_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01587 (fullRecordGapValue01587 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01587_not_prime : ¬(recordGapCenter - 328858).Prime := by
  rw [fullRecordGapTerm01587_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01587, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01587_fast_pow_mod_ne_one

def fullRecordGapValue01588 : Nat := fullRecordGapCenterValue - 328732

theorem fullRecordGapTerm01588_eq_value :
    recordGapCenter - 328732 = fullRecordGapValue01588 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01588_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01588 (fullRecordGapValue01588 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01588_not_prime : ¬(recordGapCenter - 328732).Prime := by
  rw [fullRecordGapTerm01588_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01588, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01588_fast_pow_mod_ne_one

def fullRecordGapValue01589 : Nat := fullRecordGapCenterValue - 328722

theorem fullRecordGapTerm01589_eq_value :
    recordGapCenter - 328722 = fullRecordGapValue01589 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01589_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01589 (fullRecordGapValue01589 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01589_not_prime : ¬(recordGapCenter - 328722).Prime := by
  rw [fullRecordGapTerm01589_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01589, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01589_fast_pow_mod_ne_one

def fullRecordGapValue01590 : Nat := fullRecordGapCenterValue - 328612

theorem fullRecordGapTerm01590_eq_value :
    recordGapCenter - 328612 = fullRecordGapValue01590 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01590_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01590 (fullRecordGapValue01590 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01590_not_prime : ¬(recordGapCenter - 328612).Prime := by
  rw [fullRecordGapTerm01590_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01590, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01590_fast_pow_mod_ne_one

def fullRecordGapValue01591 : Nat := fullRecordGapCenterValue - 328564

theorem fullRecordGapTerm01591_eq_value :
    recordGapCenter - 328564 = fullRecordGapValue01591 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01591_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01591 (fullRecordGapValue01591 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01591_not_prime : ¬(recordGapCenter - 328564).Prime := by
  rw [fullRecordGapTerm01591_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01591, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01591_fast_pow_mod_ne_one

def fullRecordGapValue01592 : Nat := fullRecordGapCenterValue - 328534

theorem fullRecordGapTerm01592_eq_value :
    recordGapCenter - 328534 = fullRecordGapValue01592 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01592_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01592 (fullRecordGapValue01592 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01592_not_prime : ¬(recordGapCenter - 328534).Prime := by
  rw [fullRecordGapTerm01592_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01592, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01592_fast_pow_mod_ne_one

def fullRecordGapValue01593 : Nat := fullRecordGapCenterValue - 328362

theorem fullRecordGapTerm01593_eq_value :
    recordGapCenter - 328362 = fullRecordGapValue01593 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01593_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01593 (fullRecordGapValue01593 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01593_not_prime : ¬(recordGapCenter - 328362).Prime := by
  rw [fullRecordGapTerm01593_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01593, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01593_fast_pow_mod_ne_one

def fullRecordGapValue01594 : Nat := fullRecordGapCenterValue - 328278

theorem fullRecordGapTerm01594_eq_value :
    recordGapCenter - 328278 = fullRecordGapValue01594 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01594_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01594 (fullRecordGapValue01594 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01594_not_prime : ¬(recordGapCenter - 328278).Prime := by
  rw [fullRecordGapTerm01594_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01594, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01594_fast_pow_mod_ne_one

def fullRecordGapValue01595 : Nat := fullRecordGapCenterValue - 328234

theorem fullRecordGapTerm01595_eq_value :
    recordGapCenter - 328234 = fullRecordGapValue01595 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01595_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01595 (fullRecordGapValue01595 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01595_not_prime : ¬(recordGapCenter - 328234).Prime := by
  rw [fullRecordGapTerm01595_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01595, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01595_fast_pow_mod_ne_one

def fullRecordGapValue01596 : Nat := fullRecordGapCenterValue - 328204

theorem fullRecordGapTerm01596_eq_value :
    recordGapCenter - 328204 = fullRecordGapValue01596 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01596_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01596 (fullRecordGapValue01596 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01596_not_prime : ¬(recordGapCenter - 328204).Prime := by
  rw [fullRecordGapTerm01596_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01596, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01596_fast_pow_mod_ne_one

def fullRecordGapValue01597 : Nat := fullRecordGapCenterValue - 328114

theorem fullRecordGapTerm01597_eq_value :
    recordGapCenter - 328114 = fullRecordGapValue01597 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01597_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01597 (fullRecordGapValue01597 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01597_not_prime : ¬(recordGapCenter - 328114).Prime := by
  rw [fullRecordGapTerm01597_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01597, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01597_fast_pow_mod_ne_one

def fullRecordGapValue01598 : Nat := fullRecordGapCenterValue - 328102

theorem fullRecordGapTerm01598_eq_value :
    recordGapCenter - 328102 = fullRecordGapValue01598 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01598_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01598 (fullRecordGapValue01598 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01598_not_prime : ¬(recordGapCenter - 328102).Prime := by
  rw [fullRecordGapTerm01598_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01598, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01598_fast_pow_mod_ne_one

def fullRecordGapValue01599 : Nat := fullRecordGapCenterValue - 328038

theorem fullRecordGapTerm01599_eq_value :
    recordGapCenter - 328038 = fullRecordGapValue01599 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01599_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01599 (fullRecordGapValue01599 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01599_not_prime : ¬(recordGapCenter - 328038).Prime := by
  rw [fullRecordGapTerm01599_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01599, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01599_fast_pow_mod_ne_one

def fullRecordGapValue01600 : Nat := fullRecordGapCenterValue - 327994

theorem fullRecordGapTerm01600_eq_value :
    recordGapCenter - 327994 = fullRecordGapValue01600 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01600_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01600 (fullRecordGapValue01600 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01600_not_prime : ¬(recordGapCenter - 327994).Prime := by
  rw [fullRecordGapTerm01600_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01600, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01600_fast_pow_mod_ne_one

def fullRecordGapValue01601 : Nat := fullRecordGapCenterValue - 327982

theorem fullRecordGapTerm01601_eq_value :
    recordGapCenter - 327982 = fullRecordGapValue01601 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01601_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01601 (fullRecordGapValue01601 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01601_not_prime : ¬(recordGapCenter - 327982).Prime := by
  rw [fullRecordGapTerm01601_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01601, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01601_fast_pow_mod_ne_one

def fullRecordGapValue01602 : Nat := fullRecordGapCenterValue - 327802

theorem fullRecordGapTerm01602_eq_value :
    recordGapCenter - 327802 = fullRecordGapValue01602 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01602_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01602 (fullRecordGapValue01602 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01602_not_prime : ¬(recordGapCenter - 327802).Prime := by
  rw [fullRecordGapTerm01602_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01602, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01602_fast_pow_mod_ne_one

def fullRecordGapValue01603 : Nat := fullRecordGapCenterValue - 327724

theorem fullRecordGapTerm01603_eq_value :
    recordGapCenter - 327724 = fullRecordGapValue01603 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01603_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01603 (fullRecordGapValue01603 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01603_not_prime : ¬(recordGapCenter - 327724).Prime := by
  rw [fullRecordGapTerm01603_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01603, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01603_fast_pow_mod_ne_one

def fullRecordGapValue01604 : Nat := fullRecordGapCenterValue - 327718

theorem fullRecordGapTerm01604_eq_value :
    recordGapCenter - 327718 = fullRecordGapValue01604 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01604_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01604 (fullRecordGapValue01604 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01604_not_prime : ¬(recordGapCenter - 327718).Prime := by
  rw [fullRecordGapTerm01604_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01604, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01604_fast_pow_mod_ne_one

def fullRecordGapValue01605 : Nat := fullRecordGapCenterValue - 327498

theorem fullRecordGapTerm01605_eq_value :
    recordGapCenter - 327498 = fullRecordGapValue01605 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01605_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01605 (fullRecordGapValue01605 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01605_not_prime : ¬(recordGapCenter - 327498).Prime := by
  rw [fullRecordGapTerm01605_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01605, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01605_fast_pow_mod_ne_one

def fullRecordGapValue01606 : Nat := fullRecordGapCenterValue - 327462

theorem fullRecordGapTerm01606_eq_value :
    recordGapCenter - 327462 = fullRecordGapValue01606 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01606_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01606 (fullRecordGapValue01606 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01606_not_prime : ¬(recordGapCenter - 327462).Prime := by
  rw [fullRecordGapTerm01606_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01606, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01606_fast_pow_mod_ne_one

def fullRecordGapValue01607 : Nat := fullRecordGapCenterValue - 327394

theorem fullRecordGapTerm01607_eq_value :
    recordGapCenter - 327394 = fullRecordGapValue01607 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01607_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01607 (fullRecordGapValue01607 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01607_not_prime : ¬(recordGapCenter - 327394).Prime := by
  rw [fullRecordGapTerm01607_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01607, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01607_fast_pow_mod_ne_one

def fullRecordGapValue01608 : Nat := fullRecordGapCenterValue - 327388

theorem fullRecordGapTerm01608_eq_value :
    recordGapCenter - 327388 = fullRecordGapValue01608 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01608_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01608 (fullRecordGapValue01608 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01608_not_prime : ¬(recordGapCenter - 327388).Prime := by
  rw [fullRecordGapTerm01608_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01608, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01608_fast_pow_mod_ne_one

def fullRecordGapValue01609 : Nat := fullRecordGapCenterValue - 327358

theorem fullRecordGapTerm01609_eq_value :
    recordGapCenter - 327358 = fullRecordGapValue01609 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01609_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01609 (fullRecordGapValue01609 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01609_not_prime : ¬(recordGapCenter - 327358).Prime := by
  rw [fullRecordGapTerm01609_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01609, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01609_fast_pow_mod_ne_one

def fullRecordGapValue01610 : Nat := fullRecordGapCenterValue - 327322

theorem fullRecordGapTerm01610_eq_value :
    recordGapCenter - 327322 = fullRecordGapValue01610 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01610_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01610 (fullRecordGapValue01610 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01610_not_prime : ¬(recordGapCenter - 327322).Prime := by
  rw [fullRecordGapTerm01610_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01610, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01610_fast_pow_mod_ne_one

def fullRecordGapValue01611 : Nat := fullRecordGapCenterValue - 327282

theorem fullRecordGapTerm01611_eq_value :
    recordGapCenter - 327282 = fullRecordGapValue01611 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01611_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01611 (fullRecordGapValue01611 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01611_not_prime : ¬(recordGapCenter - 327282).Prime := by
  rw [fullRecordGapTerm01611_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01611, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01611_fast_pow_mod_ne_one

def fullRecordGapValue01612 : Nat := fullRecordGapCenterValue - 327274

theorem fullRecordGapTerm01612_eq_value :
    recordGapCenter - 327274 = fullRecordGapValue01612 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01612_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01612 (fullRecordGapValue01612 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01612_not_prime : ¬(recordGapCenter - 327274).Prime := by
  rw [fullRecordGapTerm01612_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01612, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01612_fast_pow_mod_ne_one

def fullRecordGapValue01613 : Nat := fullRecordGapCenterValue - 327018

theorem fullRecordGapTerm01613_eq_value :
    recordGapCenter - 327018 = fullRecordGapValue01613 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01613_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01613 (fullRecordGapValue01613 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01613_not_prime : ¬(recordGapCenter - 327018).Prime := by
  rw [fullRecordGapTerm01613_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01613, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01613_fast_pow_mod_ne_one

def fullRecordGapValue01614 : Nat := fullRecordGapCenterValue - 326994

theorem fullRecordGapTerm01614_eq_value :
    recordGapCenter - 326994 = fullRecordGapValue01614 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01614_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01614 (fullRecordGapValue01614 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01614_not_prime : ¬(recordGapCenter - 326994).Prime := by
  rw [fullRecordGapTerm01614_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01614, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01614_fast_pow_mod_ne_one

def fullRecordGapValue01615 : Nat := fullRecordGapCenterValue - 326812

theorem fullRecordGapTerm01615_eq_value :
    recordGapCenter - 326812 = fullRecordGapValue01615 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01615_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01615 (fullRecordGapValue01615 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01615_not_prime : ¬(recordGapCenter - 326812).Prime := by
  rw [fullRecordGapTerm01615_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01615, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01615_fast_pow_mod_ne_one

def fullRecordGapValue01616 : Nat := fullRecordGapCenterValue - 326734

theorem fullRecordGapTerm01616_eq_value :
    recordGapCenter - 326734 = fullRecordGapValue01616 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01616_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01616 (fullRecordGapValue01616 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01616_not_prime : ¬(recordGapCenter - 326734).Prime := by
  rw [fullRecordGapTerm01616_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01616, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01616_fast_pow_mod_ne_one

def fullRecordGapValue01617 : Nat := fullRecordGapCenterValue - 326694

theorem fullRecordGapTerm01617_eq_value :
    recordGapCenter - 326694 = fullRecordGapValue01617 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01617_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01617 (fullRecordGapValue01617 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01617_not_prime : ¬(recordGapCenter - 326694).Prime := by
  rw [fullRecordGapTerm01617_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01617, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01617_fast_pow_mod_ne_one

def fullRecordGapValue01618 : Nat := fullRecordGapCenterValue - 326514

theorem fullRecordGapTerm01618_eq_value :
    recordGapCenter - 326514 = fullRecordGapValue01618 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01618_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01618 (fullRecordGapValue01618 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01618_not_prime : ¬(recordGapCenter - 326514).Prime := by
  rw [fullRecordGapTerm01618_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01618, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01618_fast_pow_mod_ne_one

def fullRecordGapValue01619 : Nat := fullRecordGapCenterValue - 326478

theorem fullRecordGapTerm01619_eq_value :
    recordGapCenter - 326478 = fullRecordGapValue01619 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01619_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01619 (fullRecordGapValue01619 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01619_not_prime : ¬(recordGapCenter - 326478).Prime := by
  rw [fullRecordGapTerm01619_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01619, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01619_fast_pow_mod_ne_one

def fullRecordGapValue01620 : Nat := fullRecordGapCenterValue - 326422

theorem fullRecordGapTerm01620_eq_value :
    recordGapCenter - 326422 = fullRecordGapValue01620 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01620_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01620 (fullRecordGapValue01620 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01620_not_prime : ¬(recordGapCenter - 326422).Prime := by
  rw [fullRecordGapTerm01620_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01620, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01620_fast_pow_mod_ne_one

def fullRecordGapValue01621 : Nat := fullRecordGapCenterValue - 326338

theorem fullRecordGapTerm01621_eq_value :
    recordGapCenter - 326338 = fullRecordGapValue01621 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01621_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01621 (fullRecordGapValue01621 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01621_not_prime : ¬(recordGapCenter - 326338).Prime := by
  rw [fullRecordGapTerm01621_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01621, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01621_fast_pow_mod_ne_one

def fullRecordGapValue01622 : Nat := fullRecordGapCenterValue - 326254

theorem fullRecordGapTerm01622_eq_value :
    recordGapCenter - 326254 = fullRecordGapValue01622 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01622_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01622 (fullRecordGapValue01622 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01622_not_prime : ¬(recordGapCenter - 326254).Prime := by
  rw [fullRecordGapTerm01622_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01622, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01622_fast_pow_mod_ne_one

def fullRecordGapValue01623 : Nat := fullRecordGapCenterValue - 326212

theorem fullRecordGapTerm01623_eq_value :
    recordGapCenter - 326212 = fullRecordGapValue01623 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01623_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01623 (fullRecordGapValue01623 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01623_not_prime : ¬(recordGapCenter - 326212).Prime := by
  rw [fullRecordGapTerm01623_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01623, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01623_fast_pow_mod_ne_one

def fullRecordGapValue01624 : Nat := fullRecordGapCenterValue - 326202

theorem fullRecordGapTerm01624_eq_value :
    recordGapCenter - 326202 = fullRecordGapValue01624 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01624_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01624 (fullRecordGapValue01624 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01624_not_prime : ¬(recordGapCenter - 326202).Prime := by
  rw [fullRecordGapTerm01624_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01624, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01624_fast_pow_mod_ne_one

def fullRecordGapValue01625 : Nat := fullRecordGapCenterValue - 326122

theorem fullRecordGapTerm01625_eq_value :
    recordGapCenter - 326122 = fullRecordGapValue01625 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01625_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01625 (fullRecordGapValue01625 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01625_not_prime : ¬(recordGapCenter - 326122).Prime := by
  rw [fullRecordGapTerm01625_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01625, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01625_fast_pow_mod_ne_one

def fullRecordGapValue01626 : Nat := fullRecordGapCenterValue - 326038

theorem fullRecordGapTerm01626_eq_value :
    recordGapCenter - 326038 = fullRecordGapValue01626 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01626_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01626 (fullRecordGapValue01626 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01626_not_prime : ¬(recordGapCenter - 326038).Prime := by
  rw [fullRecordGapTerm01626_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01626, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01626_fast_pow_mod_ne_one

def fullRecordGapValue01627 : Nat := fullRecordGapCenterValue - 325938

theorem fullRecordGapTerm01627_eq_value :
    recordGapCenter - 325938 = fullRecordGapValue01627 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01627_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01627 (fullRecordGapValue01627 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01627_not_prime : ¬(recordGapCenter - 325938).Prime := by
  rw [fullRecordGapTerm01627_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01627, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01627_fast_pow_mod_ne_one

def fullRecordGapValue01628 : Nat := fullRecordGapCenterValue - 325828

theorem fullRecordGapTerm01628_eq_value :
    recordGapCenter - 325828 = fullRecordGapValue01628 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01628_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01628 (fullRecordGapValue01628 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01628_not_prime : ¬(recordGapCenter - 325828).Prime := by
  rw [fullRecordGapTerm01628_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01628, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01628_fast_pow_mod_ne_one

def fullRecordGapValue01629 : Nat := fullRecordGapCenterValue - 325614

theorem fullRecordGapTerm01629_eq_value :
    recordGapCenter - 325614 = fullRecordGapValue01629 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01629_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01629 (fullRecordGapValue01629 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01629_not_prime : ¬(recordGapCenter - 325614).Prime := by
  rw [fullRecordGapTerm01629_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01629, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01629_fast_pow_mod_ne_one

def fullRecordGapValue01630 : Nat := fullRecordGapCenterValue - 325498

theorem fullRecordGapTerm01630_eq_value :
    recordGapCenter - 325498 = fullRecordGapValue01630 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01630_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01630 (fullRecordGapValue01630 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01630_not_prime : ¬(recordGapCenter - 325498).Prime := by
  rw [fullRecordGapTerm01630_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01630, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01630_fast_pow_mod_ne_one

def fullRecordGapValue01631 : Nat := fullRecordGapCenterValue - 325462

theorem fullRecordGapTerm01631_eq_value :
    recordGapCenter - 325462 = fullRecordGapValue01631 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01631_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01631 (fullRecordGapValue01631 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01631_not_prime : ¬(recordGapCenter - 325462).Prime := by
  rw [fullRecordGapTerm01631_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01631, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01631_fast_pow_mod_ne_one

def fullRecordGapValue01632 : Nat := fullRecordGapCenterValue - 325372

theorem fullRecordGapTerm01632_eq_value :
    recordGapCenter - 325372 = fullRecordGapValue01632 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01632_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01632 (fullRecordGapValue01632 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01632_not_prime : ¬(recordGapCenter - 325372).Prime := by
  rw [fullRecordGapTerm01632_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01632, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01632_fast_pow_mod_ne_one

def fullRecordGapValue01633 : Nat := fullRecordGapCenterValue - 325302

theorem fullRecordGapTerm01633_eq_value :
    recordGapCenter - 325302 = fullRecordGapValue01633 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01633_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01633 (fullRecordGapValue01633 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01633_not_prime : ¬(recordGapCenter - 325302).Prime := by
  rw [fullRecordGapTerm01633_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01633, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01633_fast_pow_mod_ne_one

def fullRecordGapValue01634 : Nat := fullRecordGapCenterValue - 325282

theorem fullRecordGapTerm01634_eq_value :
    recordGapCenter - 325282 = fullRecordGapValue01634 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01634_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01634 (fullRecordGapValue01634 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01634_not_prime : ¬(recordGapCenter - 325282).Prime := by
  rw [fullRecordGapTerm01634_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01634, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01634_fast_pow_mod_ne_one

def fullRecordGapValue01635 : Nat := fullRecordGapCenterValue - 325258

theorem fullRecordGapTerm01635_eq_value :
    recordGapCenter - 325258 = fullRecordGapValue01635 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01635_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01635 (fullRecordGapValue01635 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01635_not_prime : ¬(recordGapCenter - 325258).Prime := by
  rw [fullRecordGapTerm01635_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01635, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01635_fast_pow_mod_ne_one

def fullRecordGapValue01636 : Nat := fullRecordGapCenterValue - 325132

theorem fullRecordGapTerm01636_eq_value :
    recordGapCenter - 325132 = fullRecordGapValue01636 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01636_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01636 (fullRecordGapValue01636 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01636_not_prime : ¬(recordGapCenter - 325132).Prime := by
  rw [fullRecordGapTerm01636_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01636, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01636_fast_pow_mod_ne_one

def fullRecordGapValue01637 : Nat := fullRecordGapCenterValue - 325002

theorem fullRecordGapTerm01637_eq_value :
    recordGapCenter - 325002 = fullRecordGapValue01637 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01637_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01637 (fullRecordGapValue01637 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01637_not_prime : ¬(recordGapCenter - 325002).Prime := by
  rw [fullRecordGapTerm01637_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01637, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01637_fast_pow_mod_ne_one

def fullRecordGapValue01638 : Nat := fullRecordGapCenterValue - 324798

theorem fullRecordGapTerm01638_eq_value :
    recordGapCenter - 324798 = fullRecordGapValue01638 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01638_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01638 (fullRecordGapValue01638 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01638_not_prime : ¬(recordGapCenter - 324798).Prime := by
  rw [fullRecordGapTerm01638_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01638, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01638_fast_pow_mod_ne_one

def fullRecordGapValue01639 : Nat := fullRecordGapCenterValue - 324778

theorem fullRecordGapTerm01639_eq_value :
    recordGapCenter - 324778 = fullRecordGapValue01639 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01639_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01639 (fullRecordGapValue01639 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01639_not_prime : ¬(recordGapCenter - 324778).Prime := by
  rw [fullRecordGapTerm01639_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01639, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01639_fast_pow_mod_ne_one

def fullRecordGapValue01640 : Nat := fullRecordGapCenterValue - 324718

theorem fullRecordGapTerm01640_eq_value :
    recordGapCenter - 324718 = fullRecordGapValue01640 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01640_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01640 (fullRecordGapValue01640 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01640_not_prime : ¬(recordGapCenter - 324718).Prime := by
  rw [fullRecordGapTerm01640_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01640, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01640_fast_pow_mod_ne_one

def fullRecordGapValue01641 : Nat := fullRecordGapCenterValue - 324652

theorem fullRecordGapTerm01641_eq_value :
    recordGapCenter - 324652 = fullRecordGapValue01641 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01641_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01641 (fullRecordGapValue01641 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01641_not_prime : ¬(recordGapCenter - 324652).Prime := by
  rw [fullRecordGapTerm01641_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01641, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01641_fast_pow_mod_ne_one

def fullRecordGapValue01642 : Nat := fullRecordGapCenterValue - 324628

theorem fullRecordGapTerm01642_eq_value :
    recordGapCenter - 324628 = fullRecordGapValue01642 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01642_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01642 (fullRecordGapValue01642 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01642_not_prime : ¬(recordGapCenter - 324628).Prime := by
  rw [fullRecordGapTerm01642_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01642, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01642_fast_pow_mod_ne_one

def fullRecordGapValue01643 : Nat := fullRecordGapCenterValue - 324538

theorem fullRecordGapTerm01643_eq_value :
    recordGapCenter - 324538 = fullRecordGapValue01643 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01643_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01643 (fullRecordGapValue01643 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01643_not_prime : ¬(recordGapCenter - 324538).Prime := by
  rw [fullRecordGapTerm01643_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01643, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01643_fast_pow_mod_ne_one

def fullRecordGapValue01644 : Nat := fullRecordGapCenterValue - 324498

theorem fullRecordGapTerm01644_eq_value :
    recordGapCenter - 324498 = fullRecordGapValue01644 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01644_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01644 (fullRecordGapValue01644 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01644_not_prime : ¬(recordGapCenter - 324498).Prime := by
  rw [fullRecordGapTerm01644_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01644, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01644_fast_pow_mod_ne_one

def fullRecordGapValue01645 : Nat := fullRecordGapCenterValue - 324442

theorem fullRecordGapTerm01645_eq_value :
    recordGapCenter - 324442 = fullRecordGapValue01645 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01645_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01645 (fullRecordGapValue01645 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01645_not_prime : ¬(recordGapCenter - 324442).Prime := by
  rw [fullRecordGapTerm01645_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01645, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01645_fast_pow_mod_ne_one

def fullRecordGapValue01646 : Nat := fullRecordGapCenterValue - 324354

theorem fullRecordGapTerm01646_eq_value :
    recordGapCenter - 324354 = fullRecordGapValue01646 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01646_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01646 (fullRecordGapValue01646 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01646_not_prime : ¬(recordGapCenter - 324354).Prime := by
  rw [fullRecordGapTerm01646_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01646, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01646_fast_pow_mod_ne_one

def fullRecordGapValue01647 : Nat := fullRecordGapCenterValue - 324238

theorem fullRecordGapTerm01647_eq_value :
    recordGapCenter - 324238 = fullRecordGapValue01647 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01647_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01647 (fullRecordGapValue01647 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01647_not_prime : ¬(recordGapCenter - 324238).Prime := by
  rw [fullRecordGapTerm01647_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01647, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01647_fast_pow_mod_ne_one

def fullRecordGapValue01648 : Nat := fullRecordGapCenterValue - 324172

theorem fullRecordGapTerm01648_eq_value :
    recordGapCenter - 324172 = fullRecordGapValue01648 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01648_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01648 (fullRecordGapValue01648 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01648_not_prime : ¬(recordGapCenter - 324172).Prime := by
  rw [fullRecordGapTerm01648_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01648, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01648_fast_pow_mod_ne_one

def fullRecordGapValue01649 : Nat := fullRecordGapCenterValue - 324118

theorem fullRecordGapTerm01649_eq_value :
    recordGapCenter - 324118 = fullRecordGapValue01649 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01649_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01649 (fullRecordGapValue01649 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01649_not_prime : ¬(recordGapCenter - 324118).Prime := by
  rw [fullRecordGapTerm01649_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01649, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01649_fast_pow_mod_ne_one

def fullRecordGapValue01650 : Nat := fullRecordGapCenterValue - 324078

theorem fullRecordGapTerm01650_eq_value :
    recordGapCenter - 324078 = fullRecordGapValue01650 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01650_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01650 (fullRecordGapValue01650 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01650_not_prime : ¬(recordGapCenter - 324078).Prime := by
  rw [fullRecordGapTerm01650_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01650, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01650_fast_pow_mod_ne_one

def fullRecordGapValue01651 : Nat := fullRecordGapCenterValue - 324034

theorem fullRecordGapTerm01651_eq_value :
    recordGapCenter - 324034 = fullRecordGapValue01651 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01651_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01651 (fullRecordGapValue01651 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01651_not_prime : ¬(recordGapCenter - 324034).Prime := by
  rw [fullRecordGapTerm01651_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01651, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01651_fast_pow_mod_ne_one

def fullRecordGapValue01652 : Nat := fullRecordGapCenterValue - 324022

theorem fullRecordGapTerm01652_eq_value :
    recordGapCenter - 324022 = fullRecordGapValue01652 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01652_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01652 (fullRecordGapValue01652 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01652_not_prime : ¬(recordGapCenter - 324022).Prime := by
  rw [fullRecordGapTerm01652_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01652, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01652_fast_pow_mod_ne_one

def fullRecordGapValue01653 : Nat := fullRecordGapCenterValue - 324000

theorem fullRecordGapTerm01653_eq_value :
    recordGapCenter - 324000 = fullRecordGapValue01653 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01653_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01653 (fullRecordGapValue01653 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01653_not_prime : ¬(recordGapCenter - 324000).Prime := by
  rw [fullRecordGapTerm01653_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01653, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01653_fast_pow_mod_ne_one

def fullRecordGapValue01654 : Nat := fullRecordGapCenterValue - 323938

theorem fullRecordGapTerm01654_eq_value :
    recordGapCenter - 323938 = fullRecordGapValue01654 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01654_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01654 (fullRecordGapValue01654 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01654_not_prime : ¬(recordGapCenter - 323938).Prime := by
  rw [fullRecordGapTerm01654_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01654, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01654_fast_pow_mod_ne_one

def fullRecordGapValue01655 : Nat := fullRecordGapCenterValue - 323812

theorem fullRecordGapTerm01655_eq_value :
    recordGapCenter - 323812 = fullRecordGapValue01655 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01655_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01655 (fullRecordGapValue01655 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01655_not_prime : ¬(recordGapCenter - 323812).Prime := by
  rw [fullRecordGapTerm01655_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01655, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01655_fast_pow_mod_ne_one

def fullRecordGapValue01656 : Nat := fullRecordGapCenterValue - 323754

theorem fullRecordGapTerm01656_eq_value :
    recordGapCenter - 323754 = fullRecordGapValue01656 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01656_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01656 (fullRecordGapValue01656 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01656_not_prime : ¬(recordGapCenter - 323754).Prime := by
  rw [fullRecordGapTerm01656_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01656, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01656_fast_pow_mod_ne_one

def fullRecordGapValue01657 : Nat := fullRecordGapCenterValue - 323692

theorem fullRecordGapTerm01657_eq_value :
    recordGapCenter - 323692 = fullRecordGapValue01657 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01657_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01657 (fullRecordGapValue01657 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01657_not_prime : ¬(recordGapCenter - 323692).Prime := by
  rw [fullRecordGapTerm01657_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01657, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01657_fast_pow_mod_ne_one

def fullRecordGapValue01658 : Nat := fullRecordGapCenterValue - 323644

theorem fullRecordGapTerm01658_eq_value :
    recordGapCenter - 323644 = fullRecordGapValue01658 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01658_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01658 (fullRecordGapValue01658 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01658_not_prime : ¬(recordGapCenter - 323644).Prime := by
  rw [fullRecordGapTerm01658_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01658, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01658_fast_pow_mod_ne_one

def fullRecordGapValue01659 : Nat := fullRecordGapCenterValue - 323542

theorem fullRecordGapTerm01659_eq_value :
    recordGapCenter - 323542 = fullRecordGapValue01659 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01659_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01659 (fullRecordGapValue01659 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01659_not_prime : ¬(recordGapCenter - 323542).Prime := by
  rw [fullRecordGapTerm01659_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01659, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01659_fast_pow_mod_ne_one

def fullRecordGapValue01660 : Nat := fullRecordGapCenterValue - 323538

theorem fullRecordGapTerm01660_eq_value :
    recordGapCenter - 323538 = fullRecordGapValue01660 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01660_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01660 (fullRecordGapValue01660 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01660_not_prime : ¬(recordGapCenter - 323538).Prime := by
  rw [fullRecordGapTerm01660_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01660, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01660_fast_pow_mod_ne_one

def fullRecordGapValue01661 : Nat := fullRecordGapCenterValue - 323502

theorem fullRecordGapTerm01661_eq_value :
    recordGapCenter - 323502 = fullRecordGapValue01661 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01661_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01661 (fullRecordGapValue01661 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01661_not_prime : ¬(recordGapCenter - 323502).Prime := by
  rw [fullRecordGapTerm01661_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01661, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01661_fast_pow_mod_ne_one

def fullRecordGapValue01662 : Nat := fullRecordGapCenterValue - 323482

theorem fullRecordGapTerm01662_eq_value :
    recordGapCenter - 323482 = fullRecordGapValue01662 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01662_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01662 (fullRecordGapValue01662 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01662_not_prime : ¬(recordGapCenter - 323482).Prime := by
  rw [fullRecordGapTerm01662_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01662, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01662_fast_pow_mod_ne_one

def fullRecordGapValue01663 : Nat := fullRecordGapCenterValue - 323458

theorem fullRecordGapTerm01663_eq_value :
    recordGapCenter - 323458 = fullRecordGapValue01663 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01663_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01663 (fullRecordGapValue01663 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01663_not_prime : ¬(recordGapCenter - 323458).Prime := by
  rw [fullRecordGapTerm01663_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01663, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01663_fast_pow_mod_ne_one

def fullRecordGapValue01664 : Nat := fullRecordGapCenterValue - 323452

theorem fullRecordGapTerm01664_eq_value :
    recordGapCenter - 323452 = fullRecordGapValue01664 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01664_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01664 (fullRecordGapValue01664 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01664_not_prime : ¬(recordGapCenter - 323452).Prime := by
  rw [fullRecordGapTerm01664_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01664, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01664_fast_pow_mod_ne_one

def fullRecordGapValue01665 : Nat := fullRecordGapCenterValue - 323322

theorem fullRecordGapTerm01665_eq_value :
    recordGapCenter - 323322 = fullRecordGapValue01665 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01665_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01665 (fullRecordGapValue01665 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01665_not_prime : ¬(recordGapCenter - 323322).Prime := by
  rw [fullRecordGapTerm01665_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01665, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01665_fast_pow_mod_ne_one

def fullRecordGapValue01666 : Nat := fullRecordGapCenterValue - 323278

theorem fullRecordGapTerm01666_eq_value :
    recordGapCenter - 323278 = fullRecordGapValue01666 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01666_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01666 (fullRecordGapValue01666 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01666_not_prime : ¬(recordGapCenter - 323278).Prime := by
  rw [fullRecordGapTerm01666_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01666, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01666_fast_pow_mod_ne_one

def fullRecordGapValue01667 : Nat := fullRecordGapCenterValue - 323094

theorem fullRecordGapTerm01667_eq_value :
    recordGapCenter - 323094 = fullRecordGapValue01667 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01667_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01667 (fullRecordGapValue01667 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01667_not_prime : ¬(recordGapCenter - 323094).Prime := by
  rw [fullRecordGapTerm01667_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01667, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01667_fast_pow_mod_ne_one

def fullRecordGapValue01668 : Nat := fullRecordGapCenterValue - 322948

theorem fullRecordGapTerm01668_eq_value :
    recordGapCenter - 322948 = fullRecordGapValue01668 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01668_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01668 (fullRecordGapValue01668 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01668_not_prime : ¬(recordGapCenter - 322948).Prime := by
  rw [fullRecordGapTerm01668_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01668, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01668_fast_pow_mod_ne_one

def fullRecordGapValue01669 : Nat := fullRecordGapCenterValue - 322914

theorem fullRecordGapTerm01669_eq_value :
    recordGapCenter - 322914 = fullRecordGapValue01669 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01669_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01669 (fullRecordGapValue01669 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01669_not_prime : ¬(recordGapCenter - 322914).Prime := by
  rw [fullRecordGapTerm01669_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01669, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01669_fast_pow_mod_ne_one

def fullRecordGapValue01670 : Nat := fullRecordGapCenterValue - 322732

theorem fullRecordGapTerm01670_eq_value :
    recordGapCenter - 322732 = fullRecordGapValue01670 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01670_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01670 (fullRecordGapValue01670 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01670_not_prime : ¬(recordGapCenter - 322732).Prime := by
  rw [fullRecordGapTerm01670_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01670, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01670_fast_pow_mod_ne_one

def fullRecordGapValue01671 : Nat := fullRecordGapCenterValue - 322698

theorem fullRecordGapTerm01671_eq_value :
    recordGapCenter - 322698 = fullRecordGapValue01671 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01671_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01671 (fullRecordGapValue01671 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01671_not_prime : ¬(recordGapCenter - 322698).Prime := by
  rw [fullRecordGapTerm01671_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01671, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01671_fast_pow_mod_ne_one

def fullRecordGapValue01672 : Nat := fullRecordGapCenterValue - 322618

theorem fullRecordGapTerm01672_eq_value :
    recordGapCenter - 322618 = fullRecordGapValue01672 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01672_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01672 (fullRecordGapValue01672 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01672_not_prime : ¬(recordGapCenter - 322618).Prime := by
  rw [fullRecordGapTerm01672_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01672, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01672_fast_pow_mod_ne_one

def fullRecordGapValue01673 : Nat := fullRecordGapCenterValue - 322534

theorem fullRecordGapTerm01673_eq_value :
    recordGapCenter - 322534 = fullRecordGapValue01673 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01673_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01673 (fullRecordGapValue01673 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01673_not_prime : ¬(recordGapCenter - 322534).Prime := by
  rw [fullRecordGapTerm01673_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01673, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01673_fast_pow_mod_ne_one

def fullRecordGapValue01674 : Nat := fullRecordGapCenterValue - 322444

theorem fullRecordGapTerm01674_eq_value :
    recordGapCenter - 322444 = fullRecordGapValue01674 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01674_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01674 (fullRecordGapValue01674 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01674_not_prime : ¬(recordGapCenter - 322444).Prime := by
  rw [fullRecordGapTerm01674_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01674, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01674_fast_pow_mod_ne_one

def fullRecordGapValue01675 : Nat := fullRecordGapCenterValue - 322402

theorem fullRecordGapTerm01675_eq_value :
    recordGapCenter - 322402 = fullRecordGapValue01675 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01675_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01675 (fullRecordGapValue01675 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01675_not_prime : ¬(recordGapCenter - 322402).Prime := by
  rw [fullRecordGapTerm01675_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01675, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01675_fast_pow_mod_ne_one

def fullRecordGapValue01676 : Nat := fullRecordGapCenterValue - 322314

theorem fullRecordGapTerm01676_eq_value :
    recordGapCenter - 322314 = fullRecordGapValue01676 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01676_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01676 (fullRecordGapValue01676 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01676_not_prime : ¬(recordGapCenter - 322314).Prime := by
  rw [fullRecordGapTerm01676_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01676, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01676_fast_pow_mod_ne_one

def fullRecordGapValue01677 : Nat := fullRecordGapCenterValue - 322228

theorem fullRecordGapTerm01677_eq_value :
    recordGapCenter - 322228 = fullRecordGapValue01677 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01677_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01677 (fullRecordGapValue01677 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01677_not_prime : ¬(recordGapCenter - 322228).Prime := by
  rw [fullRecordGapTerm01677_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01677, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01677_fast_pow_mod_ne_one

def fullRecordGapValue01678 : Nat := fullRecordGapCenterValue - 321942

theorem fullRecordGapTerm01678_eq_value :
    recordGapCenter - 321942 = fullRecordGapValue01678 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01678_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01678 (fullRecordGapValue01678 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01678_not_prime : ¬(recordGapCenter - 321942).Prime := by
  rw [fullRecordGapTerm01678_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01678, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01678_fast_pow_mod_ne_one

def fullRecordGapValue01679 : Nat := fullRecordGapCenterValue - 321702

theorem fullRecordGapTerm01679_eq_value :
    recordGapCenter - 321702 = fullRecordGapValue01679 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01679_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01679 (fullRecordGapValue01679 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01679_not_prime : ¬(recordGapCenter - 321702).Prime := by
  rw [fullRecordGapTerm01679_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01679, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01679_fast_pow_mod_ne_one

def fullRecordGapValue01680 : Nat := fullRecordGapCenterValue - 321654

theorem fullRecordGapTerm01680_eq_value :
    recordGapCenter - 321654 = fullRecordGapValue01680 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01680_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01680 (fullRecordGapValue01680 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01680_not_prime : ¬(recordGapCenter - 321654).Prime := by
  rw [fullRecordGapTerm01680_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01680, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01680_fast_pow_mod_ne_one

def fullRecordGapValue01681 : Nat := fullRecordGapCenterValue - 321634

theorem fullRecordGapTerm01681_eq_value :
    recordGapCenter - 321634 = fullRecordGapValue01681 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01681_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01681 (fullRecordGapValue01681 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01681_not_prime : ¬(recordGapCenter - 321634).Prime := by
  rw [fullRecordGapTerm01681_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01681, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01681_fast_pow_mod_ne_one

def fullRecordGapValue01682 : Nat := fullRecordGapCenterValue - 321562

theorem fullRecordGapTerm01682_eq_value :
    recordGapCenter - 321562 = fullRecordGapValue01682 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01682_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01682 (fullRecordGapValue01682 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01682_not_prime : ¬(recordGapCenter - 321562).Prime := by
  rw [fullRecordGapTerm01682_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01682, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01682_fast_pow_mod_ne_one

def fullRecordGapValue01683 : Nat := fullRecordGapCenterValue - 321558

theorem fullRecordGapTerm01683_eq_value :
    recordGapCenter - 321558 = fullRecordGapValue01683 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01683_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01683 (fullRecordGapValue01683 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01683_not_prime : ¬(recordGapCenter - 321558).Prime := by
  rw [fullRecordGapTerm01683_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01683, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01683_fast_pow_mod_ne_one

def fullRecordGapValue01684 : Nat := fullRecordGapCenterValue - 321502

theorem fullRecordGapTerm01684_eq_value :
    recordGapCenter - 321502 = fullRecordGapValue01684 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01684_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01684 (fullRecordGapValue01684 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01684_not_prime : ¬(recordGapCenter - 321502).Prime := by
  rw [fullRecordGapTerm01684_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01684, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01684_fast_pow_mod_ne_one

def fullRecordGapValue01685 : Nat := fullRecordGapCenterValue - 321478

theorem fullRecordGapTerm01685_eq_value :
    recordGapCenter - 321478 = fullRecordGapValue01685 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01685_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01685 (fullRecordGapValue01685 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01685_not_prime : ¬(recordGapCenter - 321478).Prime := by
  rw [fullRecordGapTerm01685_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01685, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01685_fast_pow_mod_ne_one

def fullRecordGapValue01686 : Nat := fullRecordGapCenterValue - 321418

theorem fullRecordGapTerm01686_eq_value :
    recordGapCenter - 321418 = fullRecordGapValue01686 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01686_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01686 (fullRecordGapValue01686 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01686_not_prime : ¬(recordGapCenter - 321418).Prime := by
  rw [fullRecordGapTerm01686_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01686, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01686_fast_pow_mod_ne_one

def fullRecordGapValue01687 : Nat := fullRecordGapCenterValue - 321394

theorem fullRecordGapTerm01687_eq_value :
    recordGapCenter - 321394 = fullRecordGapValue01687 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01687_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01687 (fullRecordGapValue01687 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01687_not_prime : ¬(recordGapCenter - 321394).Prime := by
  rw [fullRecordGapTerm01687_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01687, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01687_fast_pow_mod_ne_one

def fullRecordGapValue01688 : Nat := fullRecordGapCenterValue - 321388

theorem fullRecordGapTerm01688_eq_value :
    recordGapCenter - 321388 = fullRecordGapValue01688 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01688_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01688 (fullRecordGapValue01688 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01688_not_prime : ¬(recordGapCenter - 321388).Prime := by
  rw [fullRecordGapTerm01688_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01688, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01688_fast_pow_mod_ne_one

def fullRecordGapValue01689 : Nat := fullRecordGapCenterValue - 321274

theorem fullRecordGapTerm01689_eq_value :
    recordGapCenter - 321274 = fullRecordGapValue01689 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01689_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01689 (fullRecordGapValue01689 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01689_not_prime : ¬(recordGapCenter - 321274).Prime := by
  rw [fullRecordGapTerm01689_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01689, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01689_fast_pow_mod_ne_one

def fullRecordGapValue01690 : Nat := fullRecordGapCenterValue - 321004

theorem fullRecordGapTerm01690_eq_value :
    recordGapCenter - 321004 = fullRecordGapValue01690 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01690_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01690 (fullRecordGapValue01690 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01690_not_prime : ¬(recordGapCenter - 321004).Prime := by
  rw [fullRecordGapTerm01690_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01690, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01690_fast_pow_mod_ne_one

def fullRecordGapValue01691 : Nat := fullRecordGapCenterValue - 320932

theorem fullRecordGapTerm01691_eq_value :
    recordGapCenter - 320932 = fullRecordGapValue01691 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01691_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01691 (fullRecordGapValue01691 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01691_not_prime : ¬(recordGapCenter - 320932).Prime := by
  rw [fullRecordGapTerm01691_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01691, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01691_fast_pow_mod_ne_one

def fullRecordGapValue01692 : Nat := fullRecordGapCenterValue - 320884

theorem fullRecordGapTerm01692_eq_value :
    recordGapCenter - 320884 = fullRecordGapValue01692 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01692_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01692 (fullRecordGapValue01692 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01692_not_prime : ¬(recordGapCenter - 320884).Prime := by
  rw [fullRecordGapTerm01692_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01692, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01692_fast_pow_mod_ne_one

def fullRecordGapValue01693 : Nat := fullRecordGapCenterValue - 320668

theorem fullRecordGapTerm01693_eq_value :
    recordGapCenter - 320668 = fullRecordGapValue01693 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01693_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01693 (fullRecordGapValue01693 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01693_not_prime : ¬(recordGapCenter - 320668).Prime := by
  rw [fullRecordGapTerm01693_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01693, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01693_fast_pow_mod_ne_one

def fullRecordGapValue01694 : Nat := fullRecordGapCenterValue - 320442

theorem fullRecordGapTerm01694_eq_value :
    recordGapCenter - 320442 = fullRecordGapValue01694 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01694_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01694 (fullRecordGapValue01694 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01694_not_prime : ¬(recordGapCenter - 320442).Prime := by
  rw [fullRecordGapTerm01694_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01694, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01694_fast_pow_mod_ne_one

def fullRecordGapValue01695 : Nat := fullRecordGapCenterValue - 320308

theorem fullRecordGapTerm01695_eq_value :
    recordGapCenter - 320308 = fullRecordGapValue01695 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01695_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01695 (fullRecordGapValue01695 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01695_not_prime : ¬(recordGapCenter - 320308).Prime := by
  rw [fullRecordGapTerm01695_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01695, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01695_fast_pow_mod_ne_one

def fullRecordGapValue01696 : Nat := fullRecordGapCenterValue - 320284

theorem fullRecordGapTerm01696_eq_value :
    recordGapCenter - 320284 = fullRecordGapValue01696 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01696_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01696 (fullRecordGapValue01696 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01696_not_prime : ¬(recordGapCenter - 320284).Prime := by
  rw [fullRecordGapTerm01696_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01696, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01696_fast_pow_mod_ne_one

def fullRecordGapValue01697 : Nat := fullRecordGapCenterValue - 320262

theorem fullRecordGapTerm01697_eq_value :
    recordGapCenter - 320262 = fullRecordGapValue01697 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01697_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01697 (fullRecordGapValue01697 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01697_not_prime : ¬(recordGapCenter - 320262).Prime := by
  rw [fullRecordGapTerm01697_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01697, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01697_fast_pow_mod_ne_one

def fullRecordGapValue01698 : Nat := fullRecordGapCenterValue - 320154

theorem fullRecordGapTerm01698_eq_value :
    recordGapCenter - 320154 = fullRecordGapValue01698 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01698_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01698 (fullRecordGapValue01698 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01698_not_prime : ¬(recordGapCenter - 320154).Prime := by
  rw [fullRecordGapTerm01698_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01698, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01698_fast_pow_mod_ne_one

def fullRecordGapValue01699 : Nat := fullRecordGapCenterValue - 320098

theorem fullRecordGapTerm01699_eq_value :
    recordGapCenter - 320098 = fullRecordGapValue01699 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01699_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01699 (fullRecordGapValue01699 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01699_not_prime : ¬(recordGapCenter - 320098).Prime := by
  rw [fullRecordGapTerm01699_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01699, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01699_fast_pow_mod_ne_one

def fullRecordGapValue01700 : Nat := fullRecordGapCenterValue - 319954

theorem fullRecordGapTerm01700_eq_value :
    recordGapCenter - 319954 = fullRecordGapValue01700 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01700_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01700 (fullRecordGapValue01700 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01700_not_prime : ¬(recordGapCenter - 319954).Prime := by
  rw [fullRecordGapTerm01700_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01700, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01700_fast_pow_mod_ne_one

def fullRecordGapValue01701 : Nat := fullRecordGapCenterValue - 319938

theorem fullRecordGapTerm01701_eq_value :
    recordGapCenter - 319938 = fullRecordGapValue01701 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01701_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01701 (fullRecordGapValue01701 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01701_not_prime : ¬(recordGapCenter - 319938).Prime := by
  rw [fullRecordGapTerm01701_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01701, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01701_fast_pow_mod_ne_one

def fullRecordGapValue01702 : Nat := fullRecordGapCenterValue - 319798

theorem fullRecordGapTerm01702_eq_value :
    recordGapCenter - 319798 = fullRecordGapValue01702 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01702_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01702 (fullRecordGapValue01702 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01702_not_prime : ¬(recordGapCenter - 319798).Prime := by
  rw [fullRecordGapTerm01702_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01702, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01702_fast_pow_mod_ne_one

def fullRecordGapValue01703 : Nat := fullRecordGapCenterValue - 319582

theorem fullRecordGapTerm01703_eq_value :
    recordGapCenter - 319582 = fullRecordGapValue01703 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01703_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01703 (fullRecordGapValue01703 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01703_not_prime : ¬(recordGapCenter - 319582).Prime := by
  rw [fullRecordGapTerm01703_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01703, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01703_fast_pow_mod_ne_one

def fullRecordGapValue01704 : Nat := fullRecordGapCenterValue - 319492

theorem fullRecordGapTerm01704_eq_value :
    recordGapCenter - 319492 = fullRecordGapValue01704 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01704_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01704 (fullRecordGapValue01704 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01704_not_prime : ¬(recordGapCenter - 319492).Prime := by
  rw [fullRecordGapTerm01704_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01704, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01704_fast_pow_mod_ne_one

def fullRecordGapValue01705 : Nat := fullRecordGapCenterValue - 319402

theorem fullRecordGapTerm01705_eq_value :
    recordGapCenter - 319402 = fullRecordGapValue01705 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01705_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01705 (fullRecordGapValue01705 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01705_not_prime : ¬(recordGapCenter - 319402).Prime := by
  rw [fullRecordGapTerm01705_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01705, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01705_fast_pow_mod_ne_one

def fullRecordGapValue01706 : Nat := fullRecordGapCenterValue - 319342

theorem fullRecordGapTerm01706_eq_value :
    recordGapCenter - 319342 = fullRecordGapValue01706 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01706_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01706 (fullRecordGapValue01706 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01706_not_prime : ¬(recordGapCenter - 319342).Prime := by
  rw [fullRecordGapTerm01706_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01706, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01706_fast_pow_mod_ne_one

def fullRecordGapValue01707 : Nat := fullRecordGapCenterValue - 319234

theorem fullRecordGapTerm01707_eq_value :
    recordGapCenter - 319234 = fullRecordGapValue01707 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01707_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01707 (fullRecordGapValue01707 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01707_not_prime : ¬(recordGapCenter - 319234).Prime := by
  rw [fullRecordGapTerm01707_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01707, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01707_fast_pow_mod_ne_one

def fullRecordGapValue01708 : Nat := fullRecordGapCenterValue - 319204

theorem fullRecordGapTerm01708_eq_value :
    recordGapCenter - 319204 = fullRecordGapValue01708 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01708_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01708 (fullRecordGapValue01708 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01708_not_prime : ¬(recordGapCenter - 319204).Prime := by
  rw [fullRecordGapTerm01708_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01708, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01708_fast_pow_mod_ne_one

def fullRecordGapValue01709 : Nat := fullRecordGapCenterValue - 319108

theorem fullRecordGapTerm01709_eq_value :
    recordGapCenter - 319108 = fullRecordGapValue01709 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01709_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01709 (fullRecordGapValue01709 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01709_not_prime : ¬(recordGapCenter - 319108).Prime := by
  rw [fullRecordGapTerm01709_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01709, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01709_fast_pow_mod_ne_one

def fullRecordGapValue01710 : Nat := fullRecordGapCenterValue - 318814

theorem fullRecordGapTerm01710_eq_value :
    recordGapCenter - 318814 = fullRecordGapValue01710 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01710_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01710 (fullRecordGapValue01710 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01710_not_prime : ¬(recordGapCenter - 318814).Prime := by
  rw [fullRecordGapTerm01710_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01710, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01710_fast_pow_mod_ne_one

def fullRecordGapValue01711 : Nat := fullRecordGapCenterValue - 318778

theorem fullRecordGapTerm01711_eq_value :
    recordGapCenter - 318778 = fullRecordGapValue01711 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01711_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01711 (fullRecordGapValue01711 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01711_not_prime : ¬(recordGapCenter - 318778).Prime := by
  rw [fullRecordGapTerm01711_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01711, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01711_fast_pow_mod_ne_one

def fullRecordGapValue01712 : Nat := fullRecordGapCenterValue - 318462

theorem fullRecordGapTerm01712_eq_value :
    recordGapCenter - 318462 = fullRecordGapValue01712 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01712_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01712 (fullRecordGapValue01712 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01712_not_prime : ¬(recordGapCenter - 318462).Prime := by
  rw [fullRecordGapTerm01712_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01712, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01712_fast_pow_mod_ne_one

def fullRecordGapValue01713 : Nat := fullRecordGapCenterValue - 318414

theorem fullRecordGapTerm01713_eq_value :
    recordGapCenter - 318414 = fullRecordGapValue01713 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01713_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01713 (fullRecordGapValue01713 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01713_not_prime : ¬(recordGapCenter - 318414).Prime := by
  rw [fullRecordGapTerm01713_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01713, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01713_fast_pow_mod_ne_one

def fullRecordGapValue01714 : Nat := fullRecordGapCenterValue - 318334

theorem fullRecordGapTerm01714_eq_value :
    recordGapCenter - 318334 = fullRecordGapValue01714 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01714_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01714 (fullRecordGapValue01714 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01714_not_prime : ¬(recordGapCenter - 318334).Prime := by
  rw [fullRecordGapTerm01714_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01714, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01714_fast_pow_mod_ne_one

def fullRecordGapValue01715 : Nat := fullRecordGapCenterValue - 318244

theorem fullRecordGapTerm01715_eq_value :
    recordGapCenter - 318244 = fullRecordGapValue01715 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01715_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01715 (fullRecordGapValue01715 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01715_not_prime : ¬(recordGapCenter - 318244).Prime := by
  rw [fullRecordGapTerm01715_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01715, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01715_fast_pow_mod_ne_one

def fullRecordGapValue01716 : Nat := fullRecordGapCenterValue - 318148

theorem fullRecordGapTerm01716_eq_value :
    recordGapCenter - 318148 = fullRecordGapValue01716 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01716_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01716 (fullRecordGapValue01716 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01716_not_prime : ¬(recordGapCenter - 318148).Prime := by
  rw [fullRecordGapTerm01716_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01716, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01716_fast_pow_mod_ne_one

def fullRecordGapValue01717 : Nat := fullRecordGapCenterValue - 318034

theorem fullRecordGapTerm01717_eq_value :
    recordGapCenter - 318034 = fullRecordGapValue01717 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01717_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01717 (fullRecordGapValue01717 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01717_not_prime : ¬(recordGapCenter - 318034).Prime := by
  rw [fullRecordGapTerm01717_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01717, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01717_fast_pow_mod_ne_one

def fullRecordGapValue01718 : Nat := fullRecordGapCenterValue - 317994

theorem fullRecordGapTerm01718_eq_value :
    recordGapCenter - 317994 = fullRecordGapValue01718 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01718_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01718 (fullRecordGapValue01718 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01718_not_prime : ¬(recordGapCenter - 317994).Prime := by
  rw [fullRecordGapTerm01718_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01718, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01718_fast_pow_mod_ne_one

def fullRecordGapValue01719 : Nat := fullRecordGapCenterValue - 317818

theorem fullRecordGapTerm01719_eq_value :
    recordGapCenter - 317818 = fullRecordGapValue01719 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01719_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01719 (fullRecordGapValue01719 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01719_not_prime : ¬(recordGapCenter - 317818).Prime := by
  rw [fullRecordGapTerm01719_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01719, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01719_fast_pow_mod_ne_one

def fullRecordGapValue01720 : Nat := fullRecordGapCenterValue - 317802

theorem fullRecordGapTerm01720_eq_value :
    recordGapCenter - 317802 = fullRecordGapValue01720 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01720_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01720 (fullRecordGapValue01720 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01720_not_prime : ¬(recordGapCenter - 317802).Prime := by
  rw [fullRecordGapTerm01720_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01720, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01720_fast_pow_mod_ne_one

def fullRecordGapValue01721 : Nat := fullRecordGapCenterValue - 317554

theorem fullRecordGapTerm01721_eq_value :
    recordGapCenter - 317554 = fullRecordGapValue01721 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01721_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01721 (fullRecordGapValue01721 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01721_not_prime : ¬(recordGapCenter - 317554).Prime := by
  rw [fullRecordGapTerm01721_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01721, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01721_fast_pow_mod_ne_one

def fullRecordGapValue01722 : Nat := fullRecordGapCenterValue - 317274

theorem fullRecordGapTerm01722_eq_value :
    recordGapCenter - 317274 = fullRecordGapValue01722 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01722_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01722 (fullRecordGapValue01722 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01722_not_prime : ¬(recordGapCenter - 317274).Prime := by
  rw [fullRecordGapTerm01722_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01722, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01722_fast_pow_mod_ne_one

def fullRecordGapValue01723 : Nat := fullRecordGapCenterValue - 317154

theorem fullRecordGapTerm01723_eq_value :
    recordGapCenter - 317154 = fullRecordGapValue01723 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01723_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01723 (fullRecordGapValue01723 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01723_not_prime : ¬(recordGapCenter - 317154).Prime := by
  rw [fullRecordGapTerm01723_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01723, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01723_fast_pow_mod_ne_one

def fullRecordGapValue01724 : Nat := fullRecordGapCenterValue - 317022

theorem fullRecordGapTerm01724_eq_value :
    recordGapCenter - 317022 = fullRecordGapValue01724 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01724_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01724 (fullRecordGapValue01724 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01724_not_prime : ¬(recordGapCenter - 317022).Prime := by
  rw [fullRecordGapTerm01724_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01724, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01724_fast_pow_mod_ne_one

def fullRecordGapValue01725 : Nat := fullRecordGapCenterValue - 316978

theorem fullRecordGapTerm01725_eq_value :
    recordGapCenter - 316978 = fullRecordGapValue01725 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01725_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01725 (fullRecordGapValue01725 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01725_not_prime : ¬(recordGapCenter - 316978).Prime := by
  rw [fullRecordGapTerm01725_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01725, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01725_fast_pow_mod_ne_one

def fullRecordGapValue01726 : Nat := fullRecordGapCenterValue - 316902

theorem fullRecordGapTerm01726_eq_value :
    recordGapCenter - 316902 = fullRecordGapValue01726 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01726_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01726 (fullRecordGapValue01726 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01726_not_prime : ¬(recordGapCenter - 316902).Prime := by
  rw [fullRecordGapTerm01726_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01726, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01726_fast_pow_mod_ne_one

def fullRecordGapValue01727 : Nat := fullRecordGapCenterValue - 316858

theorem fullRecordGapTerm01727_eq_value :
    recordGapCenter - 316858 = fullRecordGapValue01727 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01727_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01727 (fullRecordGapValue01727 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01727_not_prime : ¬(recordGapCenter - 316858).Prime := by
  rw [fullRecordGapTerm01727_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01727, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01727_fast_pow_mod_ne_one

def fullRecordGapValue01728 : Nat := fullRecordGapCenterValue - 316714

theorem fullRecordGapTerm01728_eq_value :
    recordGapCenter - 316714 = fullRecordGapValue01728 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01728_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01728 (fullRecordGapValue01728 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01728_not_prime : ¬(recordGapCenter - 316714).Prime := by
  rw [fullRecordGapTerm01728_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01728, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01728_fast_pow_mod_ne_one

def fullRecordGapValue01729 : Nat := fullRecordGapCenterValue - 316698

theorem fullRecordGapTerm01729_eq_value :
    recordGapCenter - 316698 = fullRecordGapValue01729 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01729_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01729 (fullRecordGapValue01729 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01729_not_prime : ¬(recordGapCenter - 316698).Prime := by
  rw [fullRecordGapTerm01729_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01729, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01729_fast_pow_mod_ne_one

def fullRecordGapValue01730 : Nat := fullRecordGapCenterValue - 316614

theorem fullRecordGapTerm01730_eq_value :
    recordGapCenter - 316614 = fullRecordGapValue01730 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01730_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01730 (fullRecordGapValue01730 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01730_not_prime : ¬(recordGapCenter - 316614).Prime := by
  rw [fullRecordGapTerm01730_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01730, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01730_fast_pow_mod_ne_one

def fullRecordGapValue01731 : Nat := fullRecordGapCenterValue - 316612

theorem fullRecordGapTerm01731_eq_value :
    recordGapCenter - 316612 = fullRecordGapValue01731 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01731_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01731 (fullRecordGapValue01731 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01731_not_prime : ¬(recordGapCenter - 316612).Prime := by
  rw [fullRecordGapTerm01731_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01731, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01731_fast_pow_mod_ne_one

def fullRecordGapValue01732 : Nat := fullRecordGapCenterValue - 316542

theorem fullRecordGapTerm01732_eq_value :
    recordGapCenter - 316542 = fullRecordGapValue01732 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01732_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01732 (fullRecordGapValue01732 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01732_not_prime : ¬(recordGapCenter - 316542).Prime := by
  rw [fullRecordGapTerm01732_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01732, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01732_fast_pow_mod_ne_one

def fullRecordGapValue01733 : Nat := fullRecordGapCenterValue - 316362

theorem fullRecordGapTerm01733_eq_value :
    recordGapCenter - 316362 = fullRecordGapValue01733 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01733_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01733 (fullRecordGapValue01733 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01733_not_prime : ¬(recordGapCenter - 316362).Prime := by
  rw [fullRecordGapTerm01733_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01733, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01733_fast_pow_mod_ne_one

def fullRecordGapValue01734 : Nat := fullRecordGapCenterValue - 316258

theorem fullRecordGapTerm01734_eq_value :
    recordGapCenter - 316258 = fullRecordGapValue01734 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01734_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01734 (fullRecordGapValue01734 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01734_not_prime : ¬(recordGapCenter - 316258).Prime := by
  rw [fullRecordGapTerm01734_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01734, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01734_fast_pow_mod_ne_one

def fullRecordGapValue01735 : Nat := fullRecordGapCenterValue - 316252

theorem fullRecordGapTerm01735_eq_value :
    recordGapCenter - 316252 = fullRecordGapValue01735 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01735_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01735 (fullRecordGapValue01735 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01735_not_prime : ¬(recordGapCenter - 316252).Prime := by
  rw [fullRecordGapTerm01735_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01735, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01735_fast_pow_mod_ne_one

def fullRecordGapValue01736 : Nat := fullRecordGapCenterValue - 316182

theorem fullRecordGapTerm01736_eq_value :
    recordGapCenter - 316182 = fullRecordGapValue01736 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01736_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01736 (fullRecordGapValue01736 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01736_not_prime : ¬(recordGapCenter - 316182).Prime := by
  rw [fullRecordGapTerm01736_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01736, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01736_fast_pow_mod_ne_one

def fullRecordGapValue01737 : Nat := fullRecordGapCenterValue - 316038

theorem fullRecordGapTerm01737_eq_value :
    recordGapCenter - 316038 = fullRecordGapValue01737 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01737_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01737 (fullRecordGapValue01737 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01737_not_prime : ¬(recordGapCenter - 316038).Prime := by
  rw [fullRecordGapTerm01737_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01737, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01737_fast_pow_mod_ne_one

def fullRecordGapValue01738 : Nat := fullRecordGapCenterValue - 315982

theorem fullRecordGapTerm01738_eq_value :
    recordGapCenter - 315982 = fullRecordGapValue01738 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01738_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01738 (fullRecordGapValue01738 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01738_not_prime : ¬(recordGapCenter - 315982).Prime := by
  rw [fullRecordGapTerm01738_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01738, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01738_fast_pow_mod_ne_one

def fullRecordGapValue01739 : Nat := fullRecordGapCenterValue - 315762

theorem fullRecordGapTerm01739_eq_value :
    recordGapCenter - 315762 = fullRecordGapValue01739 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01739_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01739 (fullRecordGapValue01739 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01739_not_prime : ¬(recordGapCenter - 315762).Prime := by
  rw [fullRecordGapTerm01739_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01739, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01739_fast_pow_mod_ne_one

def fullRecordGapValue01740 : Nat := fullRecordGapCenterValue - 315654

theorem fullRecordGapTerm01740_eq_value :
    recordGapCenter - 315654 = fullRecordGapValue01740 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01740_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01740 (fullRecordGapValue01740 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01740_not_prime : ¬(recordGapCenter - 315654).Prime := by
  rw [fullRecordGapTerm01740_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01740, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01740_fast_pow_mod_ne_one

def fullRecordGapValue01741 : Nat := fullRecordGapCenterValue - 315598

theorem fullRecordGapTerm01741_eq_value :
    recordGapCenter - 315598 = fullRecordGapValue01741 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01741_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01741 (fullRecordGapValue01741 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01741_not_prime : ¬(recordGapCenter - 315598).Prime := by
  rw [fullRecordGapTerm01741_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01741, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01741_fast_pow_mod_ne_one

def fullRecordGapValue01742 : Nat := fullRecordGapCenterValue - 315508

theorem fullRecordGapTerm01742_eq_value :
    recordGapCenter - 315508 = fullRecordGapValue01742 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01742_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01742 (fullRecordGapValue01742 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01742_not_prime : ¬(recordGapCenter - 315508).Prime := by
  rw [fullRecordGapTerm01742_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01742, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01742_fast_pow_mod_ne_one

def fullRecordGapValue01743 : Nat := fullRecordGapCenterValue - 315474

theorem fullRecordGapTerm01743_eq_value :
    recordGapCenter - 315474 = fullRecordGapValue01743 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01743_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01743 (fullRecordGapValue01743 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01743_not_prime : ¬(recordGapCenter - 315474).Prime := by
  rw [fullRecordGapTerm01743_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01743, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01743_fast_pow_mod_ne_one

def fullRecordGapValue01744 : Nat := fullRecordGapCenterValue - 315292

theorem fullRecordGapTerm01744_eq_value :
    recordGapCenter - 315292 = fullRecordGapValue01744 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01744_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01744 (fullRecordGapValue01744 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01744_not_prime : ¬(recordGapCenter - 315292).Prime := by
  rw [fullRecordGapTerm01744_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01744, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01744_fast_pow_mod_ne_one

def fullRecordGapValue01745 : Nat := fullRecordGapCenterValue - 315174

theorem fullRecordGapTerm01745_eq_value :
    recordGapCenter - 315174 = fullRecordGapValue01745 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01745_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01745 (fullRecordGapValue01745 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01745_not_prime : ¬(recordGapCenter - 315174).Prime := by
  rw [fullRecordGapTerm01745_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01745, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01745_fast_pow_mod_ne_one

def fullRecordGapValue01746 : Nat := fullRecordGapCenterValue - 315142

theorem fullRecordGapTerm01746_eq_value :
    recordGapCenter - 315142 = fullRecordGapValue01746 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01746_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01746 (fullRecordGapValue01746 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01746_not_prime : ¬(recordGapCenter - 315142).Prime := by
  rw [fullRecordGapTerm01746_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01746, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01746_fast_pow_mod_ne_one

def fullRecordGapValue01747 : Nat := fullRecordGapCenterValue - 314914

theorem fullRecordGapTerm01747_eq_value :
    recordGapCenter - 314914 = fullRecordGapValue01747 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01747_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01747 (fullRecordGapValue01747 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01747_not_prime : ¬(recordGapCenter - 314914).Prime := by
  rw [fullRecordGapTerm01747_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01747, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01747_fast_pow_mod_ne_one

def fullRecordGapValue01748 : Nat := fullRecordGapCenterValue - 314788

theorem fullRecordGapTerm01748_eq_value :
    recordGapCenter - 314788 = fullRecordGapValue01748 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01748_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01748 (fullRecordGapValue01748 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01748_not_prime : ¬(recordGapCenter - 314788).Prime := by
  rw [fullRecordGapTerm01748_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01748, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01748_fast_pow_mod_ne_one

def fullRecordGapValue01749 : Nat := fullRecordGapCenterValue - 314718

theorem fullRecordGapTerm01749_eq_value :
    recordGapCenter - 314718 = fullRecordGapValue01749 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01749_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01749 (fullRecordGapValue01749 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01749_not_prime : ¬(recordGapCenter - 314718).Prime := by
  rw [fullRecordGapTerm01749_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01749, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01749_fast_pow_mod_ne_one

def fullRecordGapValue01750 : Nat := fullRecordGapCenterValue - 314614

theorem fullRecordGapTerm01750_eq_value :
    recordGapCenter - 314614 = fullRecordGapValue01750 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01750_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01750 (fullRecordGapValue01750 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01750_not_prime : ¬(recordGapCenter - 314614).Prime := by
  rw [fullRecordGapTerm01750_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01750, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01750_fast_pow_mod_ne_one

def fullRecordGapValue01751 : Nat := fullRecordGapCenterValue - 314554

theorem fullRecordGapTerm01751_eq_value :
    recordGapCenter - 314554 = fullRecordGapValue01751 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01751_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01751 (fullRecordGapValue01751 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01751_not_prime : ¬(recordGapCenter - 314554).Prime := by
  rw [fullRecordGapTerm01751_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01751, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01751_fast_pow_mod_ne_one

def fullRecordGapValue01752 : Nat := fullRecordGapCenterValue - 314332

theorem fullRecordGapTerm01752_eq_value :
    recordGapCenter - 314332 = fullRecordGapValue01752 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01752_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01752 (fullRecordGapValue01752 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01752_not_prime : ¬(recordGapCenter - 314332).Prime := by
  rw [fullRecordGapTerm01752_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01752, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01752_fast_pow_mod_ne_one

def fullRecordGapValue01753 : Nat := fullRecordGapCenterValue - 314284

theorem fullRecordGapTerm01753_eq_value :
    recordGapCenter - 314284 = fullRecordGapValue01753 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01753_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01753 (fullRecordGapValue01753 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01753_not_prime : ¬(recordGapCenter - 314284).Prime := by
  rw [fullRecordGapTerm01753_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01753, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01753_fast_pow_mod_ne_one

def fullRecordGapValue01754 : Nat := fullRecordGapCenterValue - 314178

theorem fullRecordGapTerm01754_eq_value :
    recordGapCenter - 314178 = fullRecordGapValue01754 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01754_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01754 (fullRecordGapValue01754 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01754_not_prime : ¬(recordGapCenter - 314178).Prime := by
  rw [fullRecordGapTerm01754_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01754, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01754_fast_pow_mod_ne_one

def fullRecordGapValue01755 : Nat := fullRecordGapCenterValue - 314068

theorem fullRecordGapTerm01755_eq_value :
    recordGapCenter - 314068 = fullRecordGapValue01755 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01755_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01755 (fullRecordGapValue01755 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01755_not_prime : ¬(recordGapCenter - 314068).Prime := by
  rw [fullRecordGapTerm01755_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01755, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01755_fast_pow_mod_ne_one

def fullRecordGapValue01756 : Nat := fullRecordGapCenterValue - 314044

theorem fullRecordGapTerm01756_eq_value :
    recordGapCenter - 314044 = fullRecordGapValue01756 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01756_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01756 (fullRecordGapValue01756 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01756_not_prime : ¬(recordGapCenter - 314044).Prime := by
  rw [fullRecordGapTerm01756_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01756, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01756_fast_pow_mod_ne_one

def fullRecordGapValue01757 : Nat := fullRecordGapCenterValue - 314038

theorem fullRecordGapTerm01757_eq_value :
    recordGapCenter - 314038 = fullRecordGapValue01757 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01757_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01757 (fullRecordGapValue01757 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01757_not_prime : ¬(recordGapCenter - 314038).Prime := by
  rw [fullRecordGapTerm01757_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01757, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01757_fast_pow_mod_ne_one

def fullRecordGapValue01758 : Nat := fullRecordGapCenterValue - 313942

theorem fullRecordGapTerm01758_eq_value :
    recordGapCenter - 313942 = fullRecordGapValue01758 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01758_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01758 (fullRecordGapValue01758 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01758_not_prime : ¬(recordGapCenter - 313942).Prime := by
  rw [fullRecordGapTerm01758_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01758, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01758_fast_pow_mod_ne_one

def fullRecordGapValue01759 : Nat := fullRecordGapCenterValue - 313798

theorem fullRecordGapTerm01759_eq_value :
    recordGapCenter - 313798 = fullRecordGapValue01759 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01759_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01759 (fullRecordGapValue01759 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01759_not_prime : ¬(recordGapCenter - 313798).Prime := by
  rw [fullRecordGapTerm01759_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01759, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01759_fast_pow_mod_ne_one

def fullRecordGapValue01760 : Nat := fullRecordGapCenterValue - 313774

theorem fullRecordGapTerm01760_eq_value :
    recordGapCenter - 313774 = fullRecordGapValue01760 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01760_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01760 (fullRecordGapValue01760 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01760_not_prime : ¬(recordGapCenter - 313774).Prime := by
  rw [fullRecordGapTerm01760_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01760, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01760_fast_pow_mod_ne_one

def fullRecordGapValue01761 : Nat := fullRecordGapCenterValue - 313602

theorem fullRecordGapTerm01761_eq_value :
    recordGapCenter - 313602 = fullRecordGapValue01761 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01761_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01761 (fullRecordGapValue01761 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01761_not_prime : ¬(recordGapCenter - 313602).Prime := by
  rw [fullRecordGapTerm01761_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01761, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01761_fast_pow_mod_ne_one

def fullRecordGapValue01762 : Nat := fullRecordGapCenterValue - 313600

theorem fullRecordGapTerm01762_eq_value :
    recordGapCenter - 313600 = fullRecordGapValue01762 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01762_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01762 (fullRecordGapValue01762 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01762_not_prime : ¬(recordGapCenter - 313600).Prime := by
  rw [fullRecordGapTerm01762_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01762, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01762_fast_pow_mod_ne_one

def fullRecordGapValue01763 : Nat := fullRecordGapCenterValue - 313422

theorem fullRecordGapTerm01763_eq_value :
    recordGapCenter - 313422 = fullRecordGapValue01763 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01763_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01763 (fullRecordGapValue01763 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01763_not_prime : ¬(recordGapCenter - 313422).Prime := by
  rw [fullRecordGapTerm01763_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01763, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01763_fast_pow_mod_ne_one

def fullRecordGapValue01764 : Nat := fullRecordGapCenterValue - 313414

theorem fullRecordGapTerm01764_eq_value :
    recordGapCenter - 313414 = fullRecordGapValue01764 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01764_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01764 (fullRecordGapValue01764 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01764_not_prime : ¬(recordGapCenter - 313414).Prime := by
  rw [fullRecordGapTerm01764_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01764, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01764_fast_pow_mod_ne_one

def fullRecordGapValue01765 : Nat := fullRecordGapCenterValue - 313338

theorem fullRecordGapTerm01765_eq_value :
    recordGapCenter - 313338 = fullRecordGapValue01765 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01765_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01765 (fullRecordGapValue01765 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01765_not_prime : ¬(recordGapCenter - 313338).Prime := by
  rw [fullRecordGapTerm01765_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01765, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01765_fast_pow_mod_ne_one

def fullRecordGapValue01766 : Nat := fullRecordGapCenterValue - 313134

theorem fullRecordGapTerm01766_eq_value :
    recordGapCenter - 313134 = fullRecordGapValue01766 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01766_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01766 (fullRecordGapValue01766 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01766_not_prime : ¬(recordGapCenter - 313134).Prime := by
  rw [fullRecordGapTerm01766_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01766, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01766_fast_pow_mod_ne_one

def fullRecordGapValue01767 : Nat := fullRecordGapCenterValue - 313078

theorem fullRecordGapTerm01767_eq_value :
    recordGapCenter - 313078 = fullRecordGapValue01767 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01767_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01767 (fullRecordGapValue01767 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01767_not_prime : ¬(recordGapCenter - 313078).Prime := by
  rw [fullRecordGapTerm01767_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01767, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01767_fast_pow_mod_ne_one

def fullRecordGapValue01768 : Nat := fullRecordGapCenterValue - 312982

theorem fullRecordGapTerm01768_eq_value :
    recordGapCenter - 312982 = fullRecordGapValue01768 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01768_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01768 (fullRecordGapValue01768 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01768_not_prime : ¬(recordGapCenter - 312982).Prime := by
  rw [fullRecordGapTerm01768_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01768, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01768_fast_pow_mod_ne_one

def fullRecordGapValue01769 : Nat := fullRecordGapCenterValue - 312934

theorem fullRecordGapTerm01769_eq_value :
    recordGapCenter - 312934 = fullRecordGapValue01769 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01769_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01769 (fullRecordGapValue01769 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01769_not_prime : ¬(recordGapCenter - 312934).Prime := by
  rw [fullRecordGapTerm01769_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01769, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01769_fast_pow_mod_ne_one

def fullRecordGapValue01770 : Nat := fullRecordGapCenterValue - 312882

theorem fullRecordGapTerm01770_eq_value :
    recordGapCenter - 312882 = fullRecordGapValue01770 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01770_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01770 (fullRecordGapValue01770 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01770_not_prime : ¬(recordGapCenter - 312882).Prime := by
  rw [fullRecordGapTerm01770_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01770, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01770_fast_pow_mod_ne_one

def fullRecordGapValue01771 : Nat := fullRecordGapCenterValue - 312874

theorem fullRecordGapTerm01771_eq_value :
    recordGapCenter - 312874 = fullRecordGapValue01771 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01771_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01771 (fullRecordGapValue01771 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01771_not_prime : ¬(recordGapCenter - 312874).Prime := by
  rw [fullRecordGapTerm01771_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01771, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01771_fast_pow_mod_ne_one

def fullRecordGapValue01772 : Nat := fullRecordGapCenterValue - 312772

theorem fullRecordGapTerm01772_eq_value :
    recordGapCenter - 312772 = fullRecordGapValue01772 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01772_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01772 (fullRecordGapValue01772 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01772_not_prime : ¬(recordGapCenter - 312772).Prime := by
  rw [fullRecordGapTerm01772_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01772, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01772_fast_pow_mod_ne_one

def fullRecordGapValue01773 : Nat := fullRecordGapCenterValue - 312484

theorem fullRecordGapTerm01773_eq_value :
    recordGapCenter - 312484 = fullRecordGapValue01773 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01773_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01773 (fullRecordGapValue01773 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01773_not_prime : ¬(recordGapCenter - 312484).Prime := by
  rw [fullRecordGapTerm01773_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01773, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01773_fast_pow_mod_ne_one

def fullRecordGapValue01774 : Nat := fullRecordGapCenterValue - 312414

theorem fullRecordGapTerm01774_eq_value :
    recordGapCenter - 312414 = fullRecordGapValue01774 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01774_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01774 (fullRecordGapValue01774 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01774_not_prime : ¬(recordGapCenter - 312414).Prime := by
  rw [fullRecordGapTerm01774_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01774, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01774_fast_pow_mod_ne_one

def fullRecordGapValue01775 : Nat := fullRecordGapCenterValue - 312342

theorem fullRecordGapTerm01775_eq_value :
    recordGapCenter - 312342 = fullRecordGapValue01775 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01775_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01775 (fullRecordGapValue01775 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01775_not_prime : ¬(recordGapCenter - 312342).Prime := by
  rw [fullRecordGapTerm01775_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01775, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01775_fast_pow_mod_ne_one

def fullRecordGapValue01776 : Nat := fullRecordGapCenterValue - 312262

theorem fullRecordGapTerm01776_eq_value :
    recordGapCenter - 312262 = fullRecordGapValue01776 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01776_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01776 (fullRecordGapValue01776 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01776_not_prime : ¬(recordGapCenter - 312262).Prime := by
  rw [fullRecordGapTerm01776_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01776, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01776_fast_pow_mod_ne_one

def fullRecordGapValue01777 : Nat := fullRecordGapCenterValue - 312142

theorem fullRecordGapTerm01777_eq_value :
    recordGapCenter - 312142 = fullRecordGapValue01777 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01777_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01777 (fullRecordGapValue01777 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01777_not_prime : ¬(recordGapCenter - 312142).Prime := by
  rw [fullRecordGapTerm01777_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01777, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01777_fast_pow_mod_ne_one

def fullRecordGapValue01778 : Nat := fullRecordGapCenterValue - 312028

theorem fullRecordGapTerm01778_eq_value :
    recordGapCenter - 312028 = fullRecordGapValue01778 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01778_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01778 (fullRecordGapValue01778 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01778_not_prime : ¬(recordGapCenter - 312028).Prime := by
  rw [fullRecordGapTerm01778_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01778, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01778_fast_pow_mod_ne_one

def fullRecordGapValue01779 : Nat := fullRecordGapCenterValue - 311908

theorem fullRecordGapTerm01779_eq_value :
    recordGapCenter - 311908 = fullRecordGapValue01779 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01779_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01779 (fullRecordGapValue01779 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01779_not_prime : ¬(recordGapCenter - 311908).Prime := by
  rw [fullRecordGapTerm01779_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01779, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01779_fast_pow_mod_ne_one

def fullRecordGapValue01780 : Nat := fullRecordGapCenterValue - 311862

theorem fullRecordGapTerm01780_eq_value :
    recordGapCenter - 311862 = fullRecordGapValue01780 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01780_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01780 (fullRecordGapValue01780 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01780_not_prime : ¬(recordGapCenter - 311862).Prime := by
  rw [fullRecordGapTerm01780_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01780, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01780_fast_pow_mod_ne_one

def fullRecordGapValue01781 : Nat := fullRecordGapCenterValue - 311850

theorem fullRecordGapTerm01781_eq_value :
    recordGapCenter - 311850 = fullRecordGapValue01781 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01781_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01781 (fullRecordGapValue01781 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01781_not_prime : ¬(recordGapCenter - 311850).Prime := by
  rw [fullRecordGapTerm01781_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01781, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01781_fast_pow_mod_ne_one

def fullRecordGapValue01782 : Nat := fullRecordGapCenterValue - 311782

theorem fullRecordGapTerm01782_eq_value :
    recordGapCenter - 311782 = fullRecordGapValue01782 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01782_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01782 (fullRecordGapValue01782 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01782_not_prime : ¬(recordGapCenter - 311782).Prime := by
  rw [fullRecordGapTerm01782_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01782, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01782_fast_pow_mod_ne_one

def fullRecordGapValue01783 : Nat := fullRecordGapCenterValue - 311602

theorem fullRecordGapTerm01783_eq_value :
    recordGapCenter - 311602 = fullRecordGapValue01783 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01783_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01783 (fullRecordGapValue01783 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01783_not_prime : ¬(recordGapCenter - 311602).Prime := by
  rw [fullRecordGapTerm01783_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01783, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01783_fast_pow_mod_ne_one

def fullRecordGapValue01784 : Nat := fullRecordGapCenterValue - 311554

theorem fullRecordGapTerm01784_eq_value :
    recordGapCenter - 311554 = fullRecordGapValue01784 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01784_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01784 (fullRecordGapValue01784 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01784_not_prime : ¬(recordGapCenter - 311554).Prime := by
  rw [fullRecordGapTerm01784_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01784, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01784_fast_pow_mod_ne_one

def fullRecordGapValue01785 : Nat := fullRecordGapCenterValue - 311478

theorem fullRecordGapTerm01785_eq_value :
    recordGapCenter - 311478 = fullRecordGapValue01785 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01785_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01785 (fullRecordGapValue01785 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01785_not_prime : ¬(recordGapCenter - 311478).Prime := by
  rw [fullRecordGapTerm01785_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01785, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01785_fast_pow_mod_ne_one

def fullRecordGapValue01786 : Nat := fullRecordGapCenterValue - 311442

theorem fullRecordGapTerm01786_eq_value :
    recordGapCenter - 311442 = fullRecordGapValue01786 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01786_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01786 (fullRecordGapValue01786 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01786_not_prime : ¬(recordGapCenter - 311442).Prime := by
  rw [fullRecordGapTerm01786_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01786, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01786_fast_pow_mod_ne_one

def fullRecordGapValue01787 : Nat := fullRecordGapCenterValue - 311434

theorem fullRecordGapTerm01787_eq_value :
    recordGapCenter - 311434 = fullRecordGapValue01787 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01787_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01787 (fullRecordGapValue01787 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01787_not_prime : ¬(recordGapCenter - 311434).Prime := by
  rw [fullRecordGapTerm01787_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01787, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01787_fast_pow_mod_ne_one

def fullRecordGapValue01788 : Nat := fullRecordGapCenterValue - 311394

theorem fullRecordGapTerm01788_eq_value :
    recordGapCenter - 311394 = fullRecordGapValue01788 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01788_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01788 (fullRecordGapValue01788 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01788_not_prime : ¬(recordGapCenter - 311394).Prime := by
  rw [fullRecordGapTerm01788_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01788, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01788_fast_pow_mod_ne_one

def fullRecordGapValue01789 : Nat := fullRecordGapCenterValue - 311218

theorem fullRecordGapTerm01789_eq_value :
    recordGapCenter - 311218 = fullRecordGapValue01789 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01789_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01789 (fullRecordGapValue01789 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01789_not_prime : ¬(recordGapCenter - 311218).Prime := by
  rw [fullRecordGapTerm01789_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01789, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01789_fast_pow_mod_ne_one

def fullRecordGapValue01790 : Nat := fullRecordGapCenterValue - 311118

theorem fullRecordGapTerm01790_eq_value :
    recordGapCenter - 311118 = fullRecordGapValue01790 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01790_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01790 (fullRecordGapValue01790 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01790_not_prime : ¬(recordGapCenter - 311118).Prime := by
  rw [fullRecordGapTerm01790_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01790, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01790_fast_pow_mod_ne_one

def fullRecordGapValue01791 : Nat := fullRecordGapCenterValue - 311034

theorem fullRecordGapTerm01791_eq_value :
    recordGapCenter - 311034 = fullRecordGapValue01791 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01791_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01791 (fullRecordGapValue01791 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01791_not_prime : ¬(recordGapCenter - 311034).Prime := by
  rw [fullRecordGapTerm01791_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01791, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01791_fast_pow_mod_ne_one

def fullRecordGapValue01792 : Nat := fullRecordGapCenterValue - 310852

theorem fullRecordGapTerm01792_eq_value :
    recordGapCenter - 310852 = fullRecordGapValue01792 := by
  rw [recordGapCenter_eq_fullRecordGapCenterValue]
  rfl

set_option maxHeartbeats 0 in
theorem fullRecordGapLiteral01792_fast_pow_mod_ne_one :
    fastPowMod 3 fullRecordGapValue01792 (fullRecordGapValue01792 - 1) ≠ 1 := by
  decide

theorem fullRecordGapTerm01792_not_prime : ¬(recordGapCenter - 310852).Prime := by
  rw [fullRecordGapTerm01792_eq_value]
  apply not_prime_of_fastPowMod_ne_one (a := 3)
  · norm_num
  · norm_num [fullRecordGapValue01792, fullRecordGapCenterValue]
  · exact fullRecordGapLiteral01792_fast_pow_mod_ne_one

end PrimeFactorUnimodality
