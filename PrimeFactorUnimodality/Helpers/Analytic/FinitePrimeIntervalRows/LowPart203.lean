import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 203 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_17123 : Nat.Prime 17123 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17123 17122 1 2 [2, 7, 1223]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 17123) ^ 8561 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8561 : ZMod 17123)
      decide
    · change IsUnit ((2 : ZMod 17123) ^ 2446 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13933 : ZMod 17123)
      decide
    · change IsUnit ((2 : ZMod 17123) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10806 : ZMod 17123)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17137 : Nat.Prime 17137 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17137 17136 1 5 [2, 2, 2, 2, 3, 3, 7, 17]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((5 : ZMod 17137) ^ 8568 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8568 : ZMod 17137)
      decide
    · change IsUnit ((5 : ZMod 17137) ^ 8568 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8568 : ZMod 17137)
      decide
    · change IsUnit ((5 : ZMod 17137) ^ 8568 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8568 : ZMod 17137)
      decide
    · change IsUnit ((5 : ZMod 17137) ^ 8568 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8568 : ZMod 17137)
      decide
    · change IsUnit ((5 : ZMod 17137) ^ 5712 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7305 : ZMod 17137)
      decide
    · change IsUnit ((5 : ZMod 17137) ^ 5712 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7305 : ZMod 17137)
      decide
    · change IsUnit ((5 : ZMod 17137) ^ 2448 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2426 : ZMod 17137)
      decide
    · change IsUnit ((5 : ZMod 17137) ^ 1008 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3987 : ZMod 17137)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17159 : Nat.Prime 17159 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17159 17158 1 7 [2, 23, 373]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((7 : ZMod 17159) ^ 8579 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8579 : ZMod 17159)
      decide
    · change IsUnit ((7 : ZMod 17159) ^ 746 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6315 : ZMod 17159)
      decide
    · change IsUnit ((7 : ZMod 17159) ^ 46 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2160 : ZMod 17159)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 17117) (q := 17123) (by exact lowPrime_17123) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17123) (q := 17137) (by exact lowPrime_17137) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17137) (q := 17159) (by exact lowPrime_17159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part11_chain :
    DusartPrimeRowsChain 17117 17159 dusartPrimeRows_16319_17158_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.empty
        norm_num
