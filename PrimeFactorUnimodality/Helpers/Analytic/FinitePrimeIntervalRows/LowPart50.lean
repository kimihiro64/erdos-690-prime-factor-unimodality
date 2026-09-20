import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 50 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_6367 : Nat.Prime 6367 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6367 6366 1 3 [2, 3, 1061]
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
    · change IsUnit ((3 : ZMod 6367) ^ 3183 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3183 : ZMod 6367)
      decide
    · change IsUnit ((3 : ZMod 6367) ^ 2122 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (256 : ZMod 6367)
      decide
    · change IsUnit ((3 : ZMod 6367) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3717 : ZMod 6367)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6373 : Nat.Prime 6373 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6373 6372 1 2 [2, 2, 3, 3, 3, 59]
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
    · change IsUnit ((2 : ZMod 6373) ^ 3186 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3186 : ZMod 6373)
      decide
    · change IsUnit ((2 : ZMod 6373) ^ 3186 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3186 : ZMod 6373)
      decide
    · change IsUnit ((2 : ZMod 6373) ^ 2124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1916 : ZMod 6373)
      decide
    · change IsUnit ((2 : ZMod 6373) ^ 2124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1916 : ZMod 6373)
      decide
    · change IsUnit ((2 : ZMod 6373) ^ 2124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1916 : ZMod 6373)
      decide
    · change IsUnit ((2 : ZMod 6373) ^ 108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2800 : ZMod 6373)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6379 : Nat.Prime 6379 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6379 6378 1 2 [2, 3, 1063]
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
    · change IsUnit ((2 : ZMod 6379) ^ 3189 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3189 : ZMod 6379)
      decide
    · change IsUnit ((2 : ZMod 6379) ^ 2126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3128 : ZMod 6379)
      decide
    · change IsUnit ((2 : ZMod 6379) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5974 : ZMod 6379)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6389 : Nat.Prime 6389 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6389 6388 1 2 [2, 2, 1597]
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
    · change IsUnit ((2 : ZMod 6389) ^ 3194 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3194 : ZMod 6389)
      decide
    · change IsUnit ((2 : ZMod 6389) ^ 3194 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3194 : ZMod 6389)
      decide
    · change IsUnit ((2 : ZMod 6389) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (426 : ZMod 6389)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6397 : Nat.Prime 6397 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6397 6396 1 2 [2, 2, 3, 13, 41]
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
    · change IsUnit ((2 : ZMod 6397) ^ 3198 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3198 : ZMod 6397)
      decide
    · change IsUnit ((2 : ZMod 6397) ^ 3198 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3198 : ZMod 6397)
      decide
    · change IsUnit ((2 : ZMod 6397) ^ 2132 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1367 : ZMod 6397)
      decide
    · change IsUnit ((2 : ZMod 6397) ^ 492 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (408 : ZMod 6397)
      decide
    · change IsUnit ((2 : ZMod 6397) ^ 156 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (581 : ZMod 6397)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6421 : Nat.Prime 6421 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6421 6420 1 6 [2, 2, 3, 5, 107]
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
    · change IsUnit ((6 : ZMod 6421) ^ 3210 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3210 : ZMod 6421)
      decide
    · change IsUnit ((6 : ZMod 6421) ^ 3210 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3210 : ZMod 6421)
      decide
    · change IsUnit ((6 : ZMod 6421) ^ 2140 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1105 : ZMod 6421)
      decide
    · change IsUnit ((6 : ZMod 6421) ^ 1284 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5845 : ZMod 6421)
      decide
    · change IsUnit ((6 : ZMod 6421) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (32 : ZMod 6421)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6427 : Nat.Prime 6427 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6427 6426 1 3 [2, 3, 3, 3, 7, 17]
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
    · change IsUnit ((3 : ZMod 6427) ^ 3213 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3213 : ZMod 6427)
      decide
    · change IsUnit ((3 : ZMod 6427) ^ 2142 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (361 : ZMod 6427)
      decide
    · change IsUnit ((3 : ZMod 6427) ^ 2142 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (361 : ZMod 6427)
      decide
    · change IsUnit ((3 : ZMod 6427) ^ 2142 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (361 : ZMod 6427)
      decide
    · change IsUnit ((3 : ZMod 6427) ^ 918 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3782 : ZMod 6427)
      decide
    · change IsUnit ((3 : ZMod 6427) ^ 378 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1797 : ZMod 6427)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6449 : Nat.Prime 6449 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6449 6448 1 3 [2, 2, 2, 2, 13, 31]
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
    · change IsUnit ((3 : ZMod 6449) ^ 3224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3224 : ZMod 6449)
      decide
    · change IsUnit ((3 : ZMod 6449) ^ 3224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3224 : ZMod 6449)
      decide
    · change IsUnit ((3 : ZMod 6449) ^ 3224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3224 : ZMod 6449)
      decide
    · change IsUnit ((3 : ZMod 6449) ^ 3224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3224 : ZMod 6449)
      decide
    · change IsUnit ((3 : ZMod 6449) ^ 496 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (706 : ZMod 6449)
      decide
    · change IsUnit ((3 : ZMod 6449) ^ 208 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5817 : ZMod 6449)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6361) (q := 6367) (by exact lowPrime_6367) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6367) (q := 6373) (by exact lowPrime_6373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6373) (q := 6379) (by exact lowPrime_6379) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6379) (q := 6389) (by exact lowPrime_6389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6389) (q := 6397) (by exact lowPrime_6397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6397) (q := 6421) (by exact lowPrime_6421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6421) (q := 6427) (by exact lowPrime_6427) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6427) (q := 6449) (by exact lowPrime_6449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part02_chain :
    DusartPrimeRowsChain 6361 6449 dusartPrimeRows_6311_6636_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6634]
        · norm_num [dusartPrimeRow_of_explicit_6634]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6634]
          · norm_num [dusartPrimeRow_of_explicit_6634]
          · apply DusartPrimeRowsChain.cons
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
