import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 208 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_22307 : Nat.Prime 22307 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22307 22306 1 2 [2, 19, 587]
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
    · change IsUnit ((2 : ZMod 22307) ^ 11153 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11153 : ZMod 22307)
      decide
    · change IsUnit ((2 : ZMod 22307) ^ 1174 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13889 : ZMod 22307)
      decide
    · change IsUnit ((2 : ZMod 22307) ^ 38 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4830 : ZMod 22307)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22343 : Nat.Prime 22343 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22343 22342 1 5 [2, 11171]
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
    · change IsUnit ((5 : ZMod 22343) ^ 11171 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11171 : ZMod 22343)
      decide
    · change IsUnit ((5 : ZMod 22343) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (931 : ZMod 22343)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22349 : Nat.Prime 22349 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22349 22348 1 2 [2, 2, 37, 151]
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
    · change IsUnit ((2 : ZMod 22349) ^ 11174 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11174 : ZMod 22349)
      decide
    · change IsUnit ((2 : ZMod 22349) ^ 11174 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11174 : ZMod 22349)
      decide
    · change IsUnit ((2 : ZMod 22349) ^ 604 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17575 : ZMod 22349)
      decide
    · change IsUnit ((2 : ZMod 22349) ^ 148 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8599 : ZMod 22349)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22367 : Nat.Prime 22367 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22367 22366 1 5 [2, 53, 211]
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
    · change IsUnit ((5 : ZMod 22367) ^ 11183 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11183 : ZMod 22367)
      decide
    · change IsUnit ((5 : ZMod 22367) ^ 422 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14036 : ZMod 22367)
      decide
    · change IsUnit ((5 : ZMod 22367) ^ 106 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4953 : ZMod 22367)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22369 : Nat.Prime 22369 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22369 22368 1 11 [2, 2, 2, 2, 2, 3, 233]
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
    · change IsUnit ((11 : ZMod 22369) ^ 11184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11184 : ZMod 22369)
      decide
    · change IsUnit ((11 : ZMod 22369) ^ 11184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11184 : ZMod 22369)
      decide
    · change IsUnit ((11 : ZMod 22369) ^ 11184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11184 : ZMod 22369)
      decide
    · change IsUnit ((11 : ZMod 22369) ^ 11184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11184 : ZMod 22369)
      decide
    · change IsUnit ((11 : ZMod 22369) ^ 11184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11184 : ZMod 22369)
      decide
    · change IsUnit ((11 : ZMod 22369) ^ 7456 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19376 : ZMod 22369)
      decide
    · change IsUnit ((11 : ZMod 22369) ^ 96 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5263 : ZMod 22369)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22381 : Nat.Prime 22381 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22381 22380 1 10 [2, 2, 3, 5, 373]
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
    · change IsUnit ((10 : ZMod 22381) ^ 11190 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11190 : ZMod 22381)
      decide
    · change IsUnit ((10 : ZMod 22381) ^ 11190 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11190 : ZMod 22381)
      decide
    · change IsUnit ((10 : ZMod 22381) ^ 7460 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18332 : ZMod 22381)
      decide
    · change IsUnit ((10 : ZMod 22381) ^ 4476 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (20919 : ZMod 22381)
      decide
    · change IsUnit ((10 : ZMod 22381) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10765 : ZMod 22381)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22391 : Nat.Prime 22391 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22391 22390 1 13 [2, 5, 2239]
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
    · change IsUnit ((13 : ZMod 22391) ^ 11195 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11195 : ZMod 22391)
      decide
    · change IsUnit ((13 : ZMod 22391) ^ 4478 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14692 : ZMod 22391)
      decide
    · change IsUnit ((13 : ZMod 22391) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4166 : ZMod 22391)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22397 : Nat.Prime 22397 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22397 22396 1 2 [2, 2, 11, 509]
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
    · change IsUnit ((2 : ZMod 22397) ^ 11198 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11198 : ZMod 22397)
      decide
    · change IsUnit ((2 : ZMod 22397) ^ 11198 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11198 : ZMod 22397)
      decide
    · change IsUnit ((2 : ZMod 22397) ^ 2036 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13246 : ZMod 22397)
      decide
    · change IsUnit ((2 : ZMod 22397) ^ 44 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14664 : ZMod 22397)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22303) (q := 22307) (by exact lowPrime_22307) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22307) (q := 22343) (by exact lowPrime_22343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22343) (q := 22349) (by exact lowPrime_22349) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22349) (q := 22367) (by exact lowPrime_22367) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22367) (q := 22369) (by exact lowPrime_22369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22369) (q := 22381) (by exact lowPrime_22381) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22381) (q := 22391) (by exact lowPrime_22391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22391) (q := 22397) (by exact lowPrime_22397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part05_chain :
    DusartPrimeRowsChain 22303 22397 dusartPrimeRows_22027_23158_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num
