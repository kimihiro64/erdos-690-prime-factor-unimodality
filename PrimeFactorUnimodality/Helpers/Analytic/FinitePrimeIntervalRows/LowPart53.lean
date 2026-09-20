import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 53 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_6607 : Nat.Prime 6607 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6607 6606 1 3 [2, 3, 3, 367]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 6607) ^ 3303 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3303 : ZMod 6607)
      decide
    · change IsUnit ((3 : ZMod 6607) ^ 2202 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3898 : ZMod 6607)
      decide
    · change IsUnit ((3 : ZMod 6607) ^ 2202 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3898 : ZMod 6607)
      decide
    · change IsUnit ((3 : ZMod 6607) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6055 : ZMod 6607)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6619 : Nat.Prime 6619 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6619 6618 1 2 [2, 3, 1103]
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
    · change IsUnit ((2 : ZMod 6619) ^ 3309 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3309 : ZMod 6619)
      decide
    · change IsUnit ((2 : ZMod 6619) ^ 2206 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4602 : ZMod 6619)
      decide
    · change IsUnit ((2 : ZMod 6619) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4938 : ZMod 6619)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6637 : Nat.Prime 6637 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6637 6636 1 2 [2, 2, 3, 7, 79]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 6637) ^ 3318 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3318 : ZMod 6637)
      decide
    · change IsUnit ((2 : ZMod 6637) ^ 3318 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3318 : ZMod 6637)
      decide
    · change IsUnit ((2 : ZMod 6637) ^ 2212 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4881 : ZMod 6637)
      decide
    · change IsUnit ((2 : ZMod 6637) ^ 948 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2523 : ZMod 6637)
      decide
    · change IsUnit ((2 : ZMod 6637) ^ 84 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2313 : ZMod 6637)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6599) (q := 6607) (by exact lowPrime_6607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6607) (q := 6619) (by exact lowPrime_6619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6619) (q := 6637) (by exact lowPrime_6637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part05_chain :
    DusartPrimeRowsChain 6599 6637 dusartPrimeRows_6311_6636_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · apply DusartPrimeRowsChain.empty
        norm_num
