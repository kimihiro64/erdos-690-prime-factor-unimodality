import PrimeFactorUnimodality.Proof.LargeRange.Generated.RecordGapPrimeList
import PrimeFactorUnimodality.Proof.LargeRange.RecordTwinStructure

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option exponentiation.threshold 1000

/-! # Ordering of the two independently certified record inputs -/

namespace PrimeFactorUnimodality

/-- The composite block used for the descent lies strictly before the record
twin used for the later ascent. -/
theorem recordGapCenter_lt_recordLower : recordGapCenter < recordLower := by
  have tail_bound : recordGapTailProduct ≤ 50000 ^ 4499 := by
    rw [recordGapTailProduct, ← recordGapPrimeList_length]
    apply List.prod_le_pow_length
    intro q q_mem
    exact (recordGapPrimeList_le_limit q q_mem).trans (by norm_num)
  have center_bound : recordGapCenter < 50000 ^ 4500 := by
    rw [recordGapCenter, show 4500 = 1 + 4499 by norm_num, pow_add, pow_one]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 587 tail_bound)
      (Nat.mul_lt_mul_right (by positivity : 0 < 50000 ^ 4499) |>.2 (by norm_num))
  have block_bound : 50000 ^ 5 < recordBase ^ 4 := by
    norm_num [recordBase]
  have power_bound : 50000 ^ 4500 < recordFactor := by
    rw [show 4500 = 5 * 900 by norm_num, pow_mul, recordFactor,
      show 4096 = 4 * 900 + 496 by norm_num, pow_add, pow_mul]
    exact lt_of_lt_of_le (Nat.pow_lt_pow_left block_bound (by norm_num))
      (by
        have base_pos : 0 < recordBase := by norm_num [recordBase]
        have extra_pos : 0 < recordBase ^ 496 := _root_.pow_pos base_pos 496
        have extra : 1 ≤ recordBase ^ 496 := by omega
        calc
          (recordBase ^ 4) ^ 900 = (recordBase ^ 4) ^ 900 * 1 := by rw [mul_one]
          _ ≤ (recordBase ^ 4) ^ 900 * recordBase ^ 496 :=
            Nat.mul_le_mul_left ((recordBase ^ 4) ^ 900) extra)
  have factor_ge_four : 4 ≤ recordFactor := by
    rw [recordFactor, show 4096 = 4095 + 1 by norm_num, pow_succ]
    have base_pos : 0 < recordBase := by norm_num [recordBase]
    have prefix_pos : 0 < recordBase ^ 4095 := _root_.pow_pos base_pos 4095
    have prefix_ge_one : 1 ≤ recordBase ^ 4095 := by omega
    have base_ge_four : 4 ≤ recordBase := by norm_num [recordBase]
    nlinarith
  have factor_lt_lower : recordFactor < recordLower := by
    rw [recordLower]
    have twice_le : recordFactor * 2 ≤ recordFactor * (recordFactor - 1) :=
      Nat.mul_le_mul_left recordFactor (by omega)
    omega
  exact center_bound.trans (power_bound.trans factor_lt_lower)

end PrimeFactorUnimodality
