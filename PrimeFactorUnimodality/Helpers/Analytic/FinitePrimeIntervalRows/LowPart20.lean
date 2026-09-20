import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 20 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_4493 : Nat.Prime 4493 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4493 4492 1 2 [2, 2, 1123]
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
    · change IsUnit ((2 : ZMod 4493) ^ 2246 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2246 : ZMod 4493)
      decide
    · change IsUnit ((2 : ZMod 4493) ^ 2246 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2246 : ZMod 4493)
      decide
    · change IsUnit ((2 : ZMod 4493) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3894 : ZMod 4493)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4507 : Nat.Prime 4507 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4507 4506 1 2 [2, 3, 751]
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
    · change IsUnit ((2 : ZMod 4507) ^ 2253 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2253 : ZMod 4507)
      decide
    · change IsUnit ((2 : ZMod 4507) ^ 1502 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3268 : ZMod 4507)
      decide
    · change IsUnit ((2 : ZMod 4507) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3577 : ZMod 4507)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4513 : Nat.Prime 4513 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4513 4512 1 7 [2, 2, 2, 2, 2, 3, 47]
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
    · change IsUnit ((7 : ZMod 4513) ^ 2256 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2256 : ZMod 4513)
      decide
    · change IsUnit ((7 : ZMod 4513) ^ 2256 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2256 : ZMod 4513)
      decide
    · change IsUnit ((7 : ZMod 4513) ^ 2256 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2256 : ZMod 4513)
      decide
    · change IsUnit ((7 : ZMod 4513) ^ 2256 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2256 : ZMod 4513)
      decide
    · change IsUnit ((7 : ZMod 4513) ^ 2256 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2256 : ZMod 4513)
      decide
    · change IsUnit ((7 : ZMod 4513) ^ 1504 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (271 : ZMod 4513)
      decide
    · change IsUnit ((7 : ZMod 4513) ^ 96 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2895 : ZMod 4513)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4517 : Nat.Prime 4517 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4517 4516 1 2 [2, 2, 1129]
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
    · change IsUnit ((2 : ZMod 4517) ^ 2258 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2258 : ZMod 4517)
      decide
    · change IsUnit ((2 : ZMod 4517) ^ 2258 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2258 : ZMod 4517)
      decide
    · change IsUnit ((2 : ZMod 4517) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2108 : ZMod 4517)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4519 : Nat.Prime 4519 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4519 4518 1 3 [2, 3, 3, 251]
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
    · change IsUnit ((3 : ZMod 4519) ^ 2259 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2259 : ZMod 4519)
      decide
    · change IsUnit ((3 : ZMod 4519) ^ 1506 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2660 : ZMod 4519)
      decide
    · change IsUnit ((3 : ZMod 4519) ^ 1506 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2660 : ZMod 4519)
      decide
    · change IsUnit ((3 : ZMod 4519) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2351 : ZMod 4519)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4523 : Nat.Prime 4523 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4523 4522 1 5 [2, 7, 17, 19]
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
    · change IsUnit ((5 : ZMod 4523) ^ 2261 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2261 : ZMod 4523)
      decide
    · change IsUnit ((5 : ZMod 4523) ^ 646 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1181 : ZMod 4523)
      decide
    · change IsUnit ((5 : ZMod 4523) ^ 266 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (466 : ZMod 4523)
      decide
    · change IsUnit ((5 : ZMod 4523) ^ 238 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4380 : ZMod 4523)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4547 : Nat.Prime 4547 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4547 4546 1 2 [2, 2273]
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
    · change IsUnit ((2 : ZMod 4547) ^ 2273 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2273 : ZMod 4547)
      decide
    · change IsUnit ((2 : ZMod 4547) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1516 : ZMod 4547)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4549 : Nat.Prime 4549 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4549 4548 1 6 [2, 2, 3, 379]
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
    · change IsUnit ((6 : ZMod 4549) ^ 2274 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2274 : ZMod 4549)
      decide
    · change IsUnit ((6 : ZMod 4549) ^ 2274 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2274 : ZMod 4549)
      decide
    · change IsUnit ((6 : ZMod 4549) ^ 1516 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3967 : ZMod 4549)
      decide
    · change IsUnit ((6 : ZMod 4549) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2908 : ZMod 4549)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4483) (q := 4493) (by exact lowPrime_4493) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4493) (q := 4507) (by exact lowPrime_4507) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4507) (q := 4513) (by exact lowPrime_4513) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4513) (q := 4517) (by exact lowPrime_4517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4517) (q := 4519) (by exact lowPrime_4519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4519) (q := 4523) (by exact lowPrime_4523) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4523) (q := 4547) (by exact lowPrime_4547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4547) (q := 4549) (by exact lowPrime_4549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part11_chain :
    DusartPrimeRowsChain 4483 4549 dusartPrimeRows_3803_4672_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num
