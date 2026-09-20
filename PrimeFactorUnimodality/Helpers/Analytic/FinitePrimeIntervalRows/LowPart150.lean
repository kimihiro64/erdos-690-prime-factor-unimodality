import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 150 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_13249 : Nat.Prime 13249 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13249 13248 1 7 [2, 2, 2, 2, 2, 2, 3, 3, 23]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((7 : ZMod 13249) ^ 6624 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6624 : ZMod 13249)
      decide
    · change IsUnit ((7 : ZMod 13249) ^ 6624 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6624 : ZMod 13249)
      decide
    · change IsUnit ((7 : ZMod 13249) ^ 6624 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6624 : ZMod 13249)
      decide
    · change IsUnit ((7 : ZMod 13249) ^ 6624 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6624 : ZMod 13249)
      decide
    · change IsUnit ((7 : ZMod 13249) ^ 6624 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6624 : ZMod 13249)
      decide
    · change IsUnit ((7 : ZMod 13249) ^ 6624 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6624 : ZMod 13249)
      decide
    · change IsUnit ((7 : ZMod 13249) ^ 4416 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1069 : ZMod 13249)
      decide
    · change IsUnit ((7 : ZMod 13249) ^ 4416 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1069 : ZMod 13249)
      decide
    · change IsUnit ((7 : ZMod 13249) ^ 576 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11912 : ZMod 13249)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13259 : Nat.Prime 13259 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13259 13258 1 6 [2, 7, 947]
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
    · change IsUnit ((6 : ZMod 13259) ^ 6629 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6629 : ZMod 13259)
      decide
    · change IsUnit ((6 : ZMod 13259) ^ 1894 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9405 : ZMod 13259)
      decide
    · change IsUnit ((6 : ZMod 13259) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4084 : ZMod 13259)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13267 : Nat.Prime 13267 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13267 13266 1 3 [2, 3, 3, 11, 67]
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
    · change IsUnit ((3 : ZMod 13267) ^ 6633 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6633 : ZMod 13267)
      decide
    · change IsUnit ((3 : ZMod 13267) ^ 4422 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13200 : ZMod 13267)
      decide
    · change IsUnit ((3 : ZMod 13267) ^ 4422 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13200 : ZMod 13267)
      decide
    · change IsUnit ((3 : ZMod 13267) ^ 1206 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5898 : ZMod 13267)
      decide
    · change IsUnit ((3 : ZMod 13267) ^ 198 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12133 : ZMod 13267)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13291 : Nat.Prime 13291 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13291 13290 1 2 [2, 3, 5, 443]
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
    · change IsUnit ((2 : ZMod 13291) ^ 6645 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6645 : ZMod 13291)
      decide
    · change IsUnit ((2 : ZMod 13291) ^ 4430 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5512 : ZMod 13291)
      decide
    · change IsUnit ((2 : ZMod 13291) ^ 2658 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8444 : ZMod 13291)
      decide
    · change IsUnit ((2 : ZMod 13291) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6881 : ZMod 13291)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13297 : Nat.Prime 13297 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13297 13296 1 5 [2, 2, 2, 2, 3, 277]
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
    · change IsUnit ((5 : ZMod 13297) ^ 6648 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6648 : ZMod 13297)
      decide
    · change IsUnit ((5 : ZMod 13297) ^ 6648 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6648 : ZMod 13297)
      decide
    · change IsUnit ((5 : ZMod 13297) ^ 6648 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6648 : ZMod 13297)
      decide
    · change IsUnit ((5 : ZMod 13297) ^ 6648 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6648 : ZMod 13297)
      decide
    · change IsUnit ((5 : ZMod 13297) ^ 4432 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3632 : ZMod 13297)
      decide
    · change IsUnit ((5 : ZMod 13297) ^ 48 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1776 : ZMod 13297)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13309 : Nat.Prime 13309 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13309 13308 1 6 [2, 2, 3, 1109]
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
    · change IsUnit ((6 : ZMod 13309) ^ 6654 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6654 : ZMod 13309)
      decide
    · change IsUnit ((6 : ZMod 13309) ^ 6654 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6654 : ZMod 13309)
      decide
    · change IsUnit ((6 : ZMod 13309) ^ 4436 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7171 : ZMod 13309)
      decide
    · change IsUnit ((6 : ZMod 13309) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10416 : ZMod 13309)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13313 : Nat.Prime 13313 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13313 13312 1 3 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 13]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 13313) ^ 6656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6656 : ZMod 13313)
      decide
    · change IsUnit ((3 : ZMod 13313) ^ 6656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6656 : ZMod 13313)
      decide
    · change IsUnit ((3 : ZMod 13313) ^ 6656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6656 : ZMod 13313)
      decide
    · change IsUnit ((3 : ZMod 13313) ^ 6656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6656 : ZMod 13313)
      decide
    · change IsUnit ((3 : ZMod 13313) ^ 6656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6656 : ZMod 13313)
      decide
    · change IsUnit ((3 : ZMod 13313) ^ 6656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6656 : ZMod 13313)
      decide
    · change IsUnit ((3 : ZMod 13313) ^ 6656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6656 : ZMod 13313)
      decide
    · change IsUnit ((3 : ZMod 13313) ^ 6656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6656 : ZMod 13313)
      decide
    · change IsUnit ((3 : ZMod 13313) ^ 6656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6656 : ZMod 13313)
      decide
    · change IsUnit ((3 : ZMod 13313) ^ 6656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6656 : ZMod 13313)
      decide
    · change IsUnit ((3 : ZMod 13313) ^ 1024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11517 : ZMod 13313)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13327 : Nat.Prime 13327 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13327 13326 1 3 [2, 3, 2221]
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
    · change IsUnit ((3 : ZMod 13327) ^ 6663 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6663 : ZMod 13327)
      decide
    · change IsUnit ((3 : ZMod 13327) ^ 4442 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12279 : ZMod 13327)
      decide
    · change IsUnit ((3 : ZMod 13327) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11295 : ZMod 13327)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13241) (q := 13249) (by exact lowPrime_13249) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13249) (q := 13259) (by exact lowPrime_13259) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13259) (q := 13267) (by exact lowPrime_13267) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13267) (q := 13291) (by exact lowPrime_13291) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13291) (q := 13297) (by exact lowPrime_13297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13297) (q := 13309) (by exact lowPrime_13309) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13309) (q := 13313) (by exact lowPrime_13313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13313) (q := 13327) (by exact lowPrime_13327) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part08_chain :
    DusartPrimeRowsChain 13241 13327 dusartPrimeRows_12713_13366_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_13359]
          · norm_num [dusartPrimeRow_of_explicit_13359]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_13359]
            · norm_num [dusartPrimeRow_of_explicit_13359]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_13359]
              · norm_num [dusartPrimeRow_of_explicit_13359]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_13359]
                · norm_num [dusartPrimeRow_of_explicit_13359]
                · apply DusartPrimeRowsChain.empty
                  norm_num
