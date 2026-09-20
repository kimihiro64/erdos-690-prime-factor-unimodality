import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 82 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_8513 : Nat.Prime 8513 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8513 8512 1 5 [2, 2, 2, 2, 2, 2, 7, 19]
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
    · change IsUnit ((5 : ZMod 8513) ^ 4256 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4256 : ZMod 8513)
      decide
    · change IsUnit ((5 : ZMod 8513) ^ 4256 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4256 : ZMod 8513)
      decide
    · change IsUnit ((5 : ZMod 8513) ^ 4256 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4256 : ZMod 8513)
      decide
    · change IsUnit ((5 : ZMod 8513) ^ 4256 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4256 : ZMod 8513)
      decide
    · change IsUnit ((5 : ZMod 8513) ^ 4256 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4256 : ZMod 8513)
      decide
    · change IsUnit ((5 : ZMod 8513) ^ 4256 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4256 : ZMod 8513)
      decide
    · change IsUnit ((5 : ZMod 8513) ^ 1216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7144 : ZMod 8513)
      decide
    · change IsUnit ((5 : ZMod 8513) ^ 448 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2070 : ZMod 8513)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8521 : Nat.Prime 8521 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8521 8520 1 13 [2, 2, 2, 3, 5, 71]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((13 : ZMod 8521) ^ 4260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4260 : ZMod 8521)
      decide
    · change IsUnit ((13 : ZMod 8521) ^ 4260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4260 : ZMod 8521)
      decide
    · change IsUnit ((13 : ZMod 8521) ^ 4260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4260 : ZMod 8521)
      decide
    · change IsUnit ((13 : ZMod 8521) ^ 2840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2165 : ZMod 8521)
      decide
    · change IsUnit ((13 : ZMod 8521) ^ 1704 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3129 : ZMod 8521)
      decide
    · change IsUnit ((13 : ZMod 8521) ^ 120 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1336 : ZMod 8521)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8501) (q := 8513) (by exact lowPrime_8513) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8513) (q := 8521) (by exact lowPrime_8521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part06_chain :
    DusartPrimeRowsChain 8501 8521 dusartPrimeRows_8111_8520_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.empty
      norm_num
