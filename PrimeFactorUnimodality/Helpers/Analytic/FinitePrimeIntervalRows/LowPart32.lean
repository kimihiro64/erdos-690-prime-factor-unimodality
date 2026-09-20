import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 32 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_5237 : Nat.Prime 5237 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5237 5236 1 3 [2, 2, 7, 11, 17]
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
    · change IsUnit ((3 : ZMod 5237) ^ 2618 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2618 : ZMod 5237)
      decide
    · change IsUnit ((3 : ZMod 5237) ^ 2618 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2618 : ZMod 5237)
      decide
    · change IsUnit ((3 : ZMod 5237) ^ 748 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (276 : ZMod 5237)
      decide
    · change IsUnit ((3 : ZMod 5237) ^ 476 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1799 : ZMod 5237)
      decide
    · change IsUnit ((3 : ZMod 5237) ^ 308 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2657 : ZMod 5237)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5261 : Nat.Prime 5261 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5261 5260 1 2 [2, 2, 5, 263]
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
    · change IsUnit ((2 : ZMod 5261) ^ 2630 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2630 : ZMod 5261)
      decide
    · change IsUnit ((2 : ZMod 5261) ^ 2630 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2630 : ZMod 5261)
      decide
    · change IsUnit ((2 : ZMod 5261) ^ 1052 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3505 : ZMod 5261)
      decide
    · change IsUnit ((2 : ZMod 5261) ^ 20 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4486 : ZMod 5261)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5273 : Nat.Prime 5273 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5273 5272 1 3 [2, 2, 2, 659]
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
    · change IsUnit ((3 : ZMod 5273) ^ 2636 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2636 : ZMod 5273)
      decide
    · change IsUnit ((3 : ZMod 5273) ^ 2636 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2636 : ZMod 5273)
      decide
    · change IsUnit ((3 : ZMod 5273) ^ 2636 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2636 : ZMod 5273)
      decide
    · change IsUnit ((3 : ZMod 5273) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4134 : ZMod 5273)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5279 : Nat.Prime 5279 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5279 5278 1 7 [2, 7, 13, 29]
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
    · change IsUnit ((7 : ZMod 5279) ^ 2639 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2639 : ZMod 5279)
      decide
    · change IsUnit ((7 : ZMod 5279) ^ 754 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2097 : ZMod 5279)
      decide
    · change IsUnit ((7 : ZMod 5279) ^ 406 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5198 : ZMod 5279)
      decide
    · change IsUnit ((7 : ZMod 5279) ^ 182 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1625 : ZMod 5279)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5281 : Nat.Prime 5281 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5281 5280 1 7 [2, 2, 2, 2, 2, 3, 5, 11]
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
    · change IsUnit ((7 : ZMod 5281) ^ 2640 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2640 : ZMod 5281)
      decide
    · change IsUnit ((7 : ZMod 5281) ^ 2640 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2640 : ZMod 5281)
      decide
    · change IsUnit ((7 : ZMod 5281) ^ 2640 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2640 : ZMod 5281)
      decide
    · change IsUnit ((7 : ZMod 5281) ^ 2640 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2640 : ZMod 5281)
      decide
    · change IsUnit ((7 : ZMod 5281) ^ 2640 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2640 : ZMod 5281)
      decide
    · change IsUnit ((7 : ZMod 5281) ^ 1760 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1292 : ZMod 5281)
      decide
    · change IsUnit ((7 : ZMod 5281) ^ 1056 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1696 : ZMod 5281)
      decide
    · change IsUnit ((7 : ZMod 5281) ^ 480 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4317 : ZMod 5281)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5297 : Nat.Prime 5297 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5297 5296 1 3 [2, 2, 2, 2, 331]
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
    · change IsUnit ((3 : ZMod 5297) ^ 2648 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2648 : ZMod 5297)
      decide
    · change IsUnit ((3 : ZMod 5297) ^ 2648 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2648 : ZMod 5297)
      decide
    · change IsUnit ((3 : ZMod 5297) ^ 2648 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2648 : ZMod 5297)
      decide
    · change IsUnit ((3 : ZMod 5297) ^ 2648 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2648 : ZMod 5297)
      decide
    · change IsUnit ((3 : ZMod 5297) ^ 16 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3776 : ZMod 5297)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5303 : Nat.Prime 5303 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5303 5302 1 5 [2, 11, 241]
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
    · change IsUnit ((5 : ZMod 5303) ^ 2651 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2651 : ZMod 5303)
      decide
    · change IsUnit ((5 : ZMod 5303) ^ 482 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1881 : ZMod 5303)
      decide
    · change IsUnit ((5 : ZMod 5303) ^ 22 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5071 : ZMod 5303)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5309 : Nat.Prime 5309 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5309 5308 1 2 [2, 2, 1327]
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
    · change IsUnit ((2 : ZMod 5309) ^ 2654 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2654 : ZMod 5309)
      decide
    · change IsUnit ((2 : ZMod 5309) ^ 2654 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2654 : ZMod 5309)
      decide
    · change IsUnit ((2 : ZMod 5309) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (354 : ZMod 5309)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5233) (q := 5237) (by exact lowPrime_5237) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5237) (q := 5261) (by exact lowPrime_5261) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5261) (q := 5273) (by exact lowPrime_5273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5273) (q := 5279) (by exact lowPrime_5279) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5279) (q := 5281) (by exact lowPrime_5281) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5281) (q := 5297) (by exact lowPrime_5297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5297) (q := 5303) (by exact lowPrime_5303) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5303) (q := 5309) (by exact lowPrime_5309) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part02_chain :
    DusartPrimeRowsChain 5233 5309 dusartPrimeRows_5167_5436_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · apply DusartPrimeRowsChain.empty
                  norm_num
