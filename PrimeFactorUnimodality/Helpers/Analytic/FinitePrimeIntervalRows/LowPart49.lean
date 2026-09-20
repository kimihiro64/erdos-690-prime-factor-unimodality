import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 49 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_6317 : Nat.Prime 6317 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6317 6316 1 2 [2, 2, 1579]
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
    · change IsUnit ((2 : ZMod 6317) ^ 3158 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3158 : ZMod 6317)
      decide
    · change IsUnit ((2 : ZMod 6317) ^ 3158 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3158 : ZMod 6317)
      decide
    · change IsUnit ((2 : ZMod 6317) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2948 : ZMod 6317)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6323 : Nat.Prime 6323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6323 6322 1 2 [2, 29, 109]
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
    · change IsUnit ((2 : ZMod 6323) ^ 3161 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3161 : ZMod 6323)
      decide
    · change IsUnit ((2 : ZMod 6323) ^ 218 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3574 : ZMod 6323)
      decide
    · change IsUnit ((2 : ZMod 6323) ^ 58 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3368 : ZMod 6323)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6329 : Nat.Prime 6329 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6329 6328 1 3 [2, 2, 2, 7, 113]
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
    · change IsUnit ((3 : ZMod 6329) ^ 3164 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3164 : ZMod 6329)
      decide
    · change IsUnit ((3 : ZMod 6329) ^ 3164 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3164 : ZMod 6329)
      decide
    · change IsUnit ((3 : ZMod 6329) ^ 3164 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3164 : ZMod 6329)
      decide
    · change IsUnit ((3 : ZMod 6329) ^ 904 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (474 : ZMod 6329)
      decide
    · change IsUnit ((3 : ZMod 6329) ^ 56 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1463 : ZMod 6329)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6337 : Nat.Prime 6337 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6337 6336 1 10 [2, 2, 2, 2, 2, 2, 3, 3, 11]
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
    · change IsUnit ((10 : ZMod 6337) ^ 3168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3168 : ZMod 6337)
      decide
    · change IsUnit ((10 : ZMod 6337) ^ 3168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3168 : ZMod 6337)
      decide
    · change IsUnit ((10 : ZMod 6337) ^ 3168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3168 : ZMod 6337)
      decide
    · change IsUnit ((10 : ZMod 6337) ^ 3168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3168 : ZMod 6337)
      decide
    · change IsUnit ((10 : ZMod 6337) ^ 3168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3168 : ZMod 6337)
      decide
    · change IsUnit ((10 : ZMod 6337) ^ 3168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3168 : ZMod 6337)
      decide
    · change IsUnit ((10 : ZMod 6337) ^ 2112 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2616 : ZMod 6337)
      decide
    · change IsUnit ((10 : ZMod 6337) ^ 2112 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2616 : ZMod 6337)
      decide
    · change IsUnit ((10 : ZMod 6337) ^ 576 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1179 : ZMod 6337)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6343 : Nat.Prime 6343 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6343 6342 1 3 [2, 3, 7, 151]
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
    · change IsUnit ((3 : ZMod 6343) ^ 3171 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3171 : ZMod 6343)
      decide
    · change IsUnit ((3 : ZMod 6343) ^ 2114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4414 : ZMod 6343)
      decide
    · change IsUnit ((3 : ZMod 6343) ^ 906 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5787 : ZMod 6343)
      decide
    · change IsUnit ((3 : ZMod 6343) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2511 : ZMod 6343)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6353 : Nat.Prime 6353 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6353 6352 1 3 [2, 2, 2, 2, 397]
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
    · change IsUnit ((3 : ZMod 6353) ^ 3176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3176 : ZMod 6353)
      decide
    · change IsUnit ((3 : ZMod 6353) ^ 3176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3176 : ZMod 6353)
      decide
    · change IsUnit ((3 : ZMod 6353) ^ 3176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3176 : ZMod 6353)
      decide
    · change IsUnit ((3 : ZMod 6353) ^ 3176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3176 : ZMod 6353)
      decide
    · change IsUnit ((3 : ZMod 6353) ^ 16 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5054 : ZMod 6353)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6359 : Nat.Prime 6359 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6359 6358 1 13 [2, 11, 17, 17]
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
    · change IsUnit ((13 : ZMod 6359) ^ 3179 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3179 : ZMod 6359)
      decide
    · change IsUnit ((13 : ZMod 6359) ^ 578 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4634 : ZMod 6359)
      decide
    · change IsUnit ((13 : ZMod 6359) ^ 374 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2617 : ZMod 6359)
      decide
    · change IsUnit ((13 : ZMod 6359) ^ 374 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2617 : ZMod 6359)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6361 : Nat.Prime 6361 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6361 6360 1 19 [2, 2, 2, 3, 5, 53]
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
    · change IsUnit ((19 : ZMod 6361) ^ 3180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3180 : ZMod 6361)
      decide
    · change IsUnit ((19 : ZMod 6361) ^ 3180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3180 : ZMod 6361)
      decide
    · change IsUnit ((19 : ZMod 6361) ^ 3180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3180 : ZMod 6361)
      decide
    · change IsUnit ((19 : ZMod 6361) ^ 2120 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5741 : ZMod 6361)
      decide
    · change IsUnit ((19 : ZMod 6361) ^ 1272 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (911 : ZMod 6361)
      decide
    · change IsUnit ((19 : ZMod 6361) ^ 120 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4265 : ZMod 6361)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6311) (q := 6317) (by exact lowPrime_6317) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6317) (q := 6323) (by exact lowPrime_6323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6323) (q := 6329) (by exact lowPrime_6329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6329) (q := 6337) (by exact lowPrime_6337) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6337) (q := 6343) (by exact lowPrime_6343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6343) (q := 6353) (by exact lowPrime_6353) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6353) (q := 6359) (by exact lowPrime_6359) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6359) (q := 6361) (by exact lowPrime_6361) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part01_chain :
    DusartPrimeRowsChain 6311 6361 dusartPrimeRows_6311_6636_part01 := by
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
