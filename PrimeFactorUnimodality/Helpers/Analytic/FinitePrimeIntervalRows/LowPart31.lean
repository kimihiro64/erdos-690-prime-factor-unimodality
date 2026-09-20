import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 31 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_5171 : Nat.Prime 5171 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5171 5170 1 2 [2, 5, 11, 47]
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
    · change IsUnit ((2 : ZMod 5171) ^ 2585 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2585 : ZMod 5171)
      decide
    · change IsUnit ((2 : ZMod 5171) ^ 1034 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3852 : ZMod 5171)
      decide
    · change IsUnit ((2 : ZMod 5171) ^ 470 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3760 : ZMod 5171)
      decide
    · change IsUnit ((2 : ZMod 5171) ^ 110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2992 : ZMod 5171)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5179 : Nat.Prime 5179 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5179 5178 1 2 [2, 3, 863]
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
    · change IsUnit ((2 : ZMod 5179) ^ 2589 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2589 : ZMod 5179)
      decide
    · change IsUnit ((2 : ZMod 5179) ^ 1726 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2953 : ZMod 5179)
      decide
    · change IsUnit ((2 : ZMod 5179) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2384 : ZMod 5179)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5189 : Nat.Prime 5189 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5189 5188 1 2 [2, 2, 1297]
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
    · change IsUnit ((2 : ZMod 5189) ^ 2594 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2594 : ZMod 5189)
      decide
    · change IsUnit ((2 : ZMod 5189) ^ 2594 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2594 : ZMod 5189)
      decide
    · change IsUnit ((2 : ZMod 5189) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (346 : ZMod 5189)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5197 : Nat.Prime 5197 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5197 5196 1 7 [2, 2, 3, 433]
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
    · change IsUnit ((7 : ZMod 5197) ^ 2598 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2598 : ZMod 5197)
      decide
    · change IsUnit ((7 : ZMod 5197) ^ 2598 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2598 : ZMod 5197)
      decide
    · change IsUnit ((7 : ZMod 5197) ^ 1732 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2838 : ZMod 5197)
      decide
    · change IsUnit ((7 : ZMod 5197) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1148 : ZMod 5197)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5209 : Nat.Prime 5209 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5209 5208 1 17 [2, 2, 2, 3, 7, 31]
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
    · change IsUnit ((17 : ZMod 5209) ^ 2604 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2604 : ZMod 5209)
      decide
    · change IsUnit ((17 : ZMod 5209) ^ 2604 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2604 : ZMod 5209)
      decide
    · change IsUnit ((17 : ZMod 5209) ^ 2604 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2604 : ZMod 5209)
      decide
    · change IsUnit ((17 : ZMod 5209) ^ 1736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (397 : ZMod 5209)
      decide
    · change IsUnit ((17 : ZMod 5209) ^ 744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1458 : ZMod 5209)
      decide
    · change IsUnit ((17 : ZMod 5209) ^ 168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4692 : ZMod 5209)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5227 : Nat.Prime 5227 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5227 5226 1 2 [2, 3, 13, 67]
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
    · change IsUnit ((2 : ZMod 5227) ^ 2613 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2613 : ZMod 5227)
      decide
    · change IsUnit ((2 : ZMod 5227) ^ 1742 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5076 : ZMod 5227)
      decide
    · change IsUnit ((2 : ZMod 5227) ^ 402 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (917 : ZMod 5227)
      decide
    · change IsUnit ((2 : ZMod 5227) ^ 78 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5132 : ZMod 5227)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5231 : Nat.Prime 5231 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5231 5230 1 7 [2, 5, 523]
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
    · change IsUnit ((7 : ZMod 5231) ^ 2615 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2615 : ZMod 5231)
      decide
    · change IsUnit ((7 : ZMod 5231) ^ 1046 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2848 : ZMod 5231)
      decide
    · change IsUnit ((7 : ZMod 5231) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5034 : ZMod 5231)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5233 : Nat.Prime 5233 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5233 5232 1 10 [2, 2, 2, 2, 3, 109]
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
    · change IsUnit ((10 : ZMod 5233) ^ 2616 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2616 : ZMod 5233)
      decide
    · change IsUnit ((10 : ZMod 5233) ^ 2616 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2616 : ZMod 5233)
      decide
    · change IsUnit ((10 : ZMod 5233) ^ 2616 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2616 : ZMod 5233)
      decide
    · change IsUnit ((10 : ZMod 5233) ^ 2616 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2616 : ZMod 5233)
      decide
    · change IsUnit ((10 : ZMod 5233) ^ 1744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (110 : ZMod 5233)
      decide
    · change IsUnit ((10 : ZMod 5233) ^ 48 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1956 : ZMod 5233)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5167) (q := 5171) (by exact lowPrime_5171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5171) (q := 5179) (by exact lowPrime_5179) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5179) (q := 5189) (by exact lowPrime_5189) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5189) (q := 5197) (by exact lowPrime_5197) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5197) (q := 5209) (by exact lowPrime_5209) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5209) (q := 5227) (by exact lowPrime_5227) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5227) (q := 5231) (by exact lowPrime_5231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5231) (q := 5233) (by exact lowPrime_5233) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part01_chain :
    DusartPrimeRowsChain 5167 5233 dusartPrimeRows_5167_5436_part01 := by
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
