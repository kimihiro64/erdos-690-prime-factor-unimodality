import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 140 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_12527 : Nat.Prime 12527 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12527 12526 1 5 [2, 6263]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · change IsUnit ((5 : ZMod 12527) ^ 6263 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6263 : ZMod 12527)
      decide
    · change IsUnit ((5 : ZMod 12527) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (522 : ZMod 12527)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12539 : Nat.Prime 12539 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12539 12538 1 2 [2, 6269]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · change IsUnit ((2 : ZMod 12539) ^ 6269 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6269 : ZMod 12539)
      decide
    · change IsUnit ((2 : ZMod 12539) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4180 : ZMod 12539)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12541 : Nat.Prime 12541 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12541 12540 1 14 [2, 2, 3, 5, 11, 19]
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
    · change IsUnit ((14 : ZMod 12541) ^ 6270 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6270 : ZMod 12541)
      decide
    · change IsUnit ((14 : ZMod 12541) ^ 6270 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6270 : ZMod 12541)
      decide
    · change IsUnit ((14 : ZMod 12541) ^ 4180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (794 : ZMod 12541)
      decide
    · change IsUnit ((14 : ZMod 12541) ^ 2508 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9909 : ZMod 12541)
      decide
    · change IsUnit ((14 : ZMod 12541) ^ 1140 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11141 : ZMod 12541)
      decide
    · change IsUnit ((14 : ZMod 12541) ^ 660 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3226 : ZMod 12541)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12547 : Nat.Prime 12547 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12547 12546 1 2 [2, 3, 3, 17, 41]
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
    · change IsUnit ((2 : ZMod 12547) ^ 6273 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6273 : ZMod 12547)
      decide
    · change IsUnit ((2 : ZMod 12547) ^ 4182 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10474 : ZMod 12547)
      decide
    · change IsUnit ((2 : ZMod 12547) ^ 4182 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10474 : ZMod 12547)
      decide
    · change IsUnit ((2 : ZMod 12547) ^ 738 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10732 : ZMod 12547)
      decide
    · change IsUnit ((2 : ZMod 12547) ^ 306 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2315 : ZMod 12547)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12553 : Nat.Prime 12553 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12553 12552 1 5 [2, 2, 2, 3, 523]
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
    · change IsUnit ((5 : ZMod 12553) ^ 6276 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6276 : ZMod 12553)
      decide
    · change IsUnit ((5 : ZMod 12553) ^ 6276 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6276 : ZMod 12553)
      decide
    · change IsUnit ((5 : ZMod 12553) ^ 6276 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6276 : ZMod 12553)
      decide
    · change IsUnit ((5 : ZMod 12553) ^ 4184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6649 : ZMod 12553)
      decide
    · change IsUnit ((5 : ZMod 12553) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8792 : ZMod 12553)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12569 : Nat.Prime 12569 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12569 12568 1 3 [2, 2, 2, 1571]
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
    · change IsUnit ((3 : ZMod 12569) ^ 6284 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6284 : ZMod 12569)
      decide
    · change IsUnit ((3 : ZMod 12569) ^ 6284 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6284 : ZMod 12569)
      decide
    · change IsUnit ((3 : ZMod 12569) ^ 6284 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6284 : ZMod 12569)
      decide
    · change IsUnit ((3 : ZMod 12569) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1209 : ZMod 12569)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12577 : Nat.Prime 12577 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12577 12576 1 10 [2, 2, 2, 2, 2, 3, 131]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((10 : ZMod 12577) ^ 6288 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6288 : ZMod 12577)
      decide
    · change IsUnit ((10 : ZMod 12577) ^ 6288 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6288 : ZMod 12577)
      decide
    · change IsUnit ((10 : ZMod 12577) ^ 6288 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6288 : ZMod 12577)
      decide
    · change IsUnit ((10 : ZMod 12577) ^ 6288 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6288 : ZMod 12577)
      decide
    · change IsUnit ((10 : ZMod 12577) ^ 6288 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6288 : ZMod 12577)
      decide
    · change IsUnit ((10 : ZMod 12577) ^ 4192 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9989 : ZMod 12577)
      decide
    · change IsUnit ((10 : ZMod 12577) ^ 96 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (286 : ZMod 12577)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12583 : Nat.Prime 12583 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12583 12582 1 5 [2, 3, 3, 3, 233]
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
    · change IsUnit ((5 : ZMod 12583) ^ 6291 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6291 : ZMod 12583)
      decide
    · change IsUnit ((5 : ZMod 12583) ^ 4194 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3628 : ZMod 12583)
      decide
    · change IsUnit ((5 : ZMod 12583) ^ 4194 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3628 : ZMod 12583)
      decide
    · change IsUnit ((5 : ZMod 12583) ^ 4194 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3628 : ZMod 12583)
      decide
    · change IsUnit ((5 : ZMod 12583) ^ 54 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3258 : ZMod 12583)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12517) (q := 12527) (by exact lowPrime_12527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12527) (q := 12539) (by exact lowPrime_12539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12539) (q := 12541) (by exact lowPrime_12541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12541) (q := 12547) (by exact lowPrime_12547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12547) (q := 12553) (by exact lowPrime_12553) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12553) (q := 12569) (by exact lowPrime_12569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12569) (q := 12577) (by exact lowPrime_12577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12577) (q := 12583) (by exact lowPrime_12583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part07_chain :
    DusartPrimeRowsChain 12517 12583 dusartPrimeRows_12097_12712_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num
