import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 193 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_16333 : Nat.Prime 16333 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16333 16332 1 2 [2, 2, 3, 1361]
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
    · change IsUnit ((2 : ZMod 16333) ^ 8166 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8166 : ZMod 16333)
      decide
    · change IsUnit ((2 : ZMod 16333) ^ 8166 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8166 : ZMod 16333)
      decide
    · change IsUnit ((2 : ZMod 16333) ^ 5444 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (516 : ZMod 16333)
      decide
    · change IsUnit ((2 : ZMod 16333) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13553 : ZMod 16333)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16339 : Nat.Prime 16339 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16339 16338 1 2 [2, 3, 7, 389]
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
    · change IsUnit ((2 : ZMod 16339) ^ 8169 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8169 : ZMod 16339)
      decide
    · change IsUnit ((2 : ZMod 16339) ^ 5446 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7817 : ZMod 16339)
      decide
    · change IsUnit ((2 : ZMod 16339) ^ 2334 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5072 : ZMod 16339)
      decide
    · change IsUnit ((2 : ZMod 16339) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14445 : ZMod 16339)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16349 : Nat.Prime 16349 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16349 16348 1 2 [2, 2, 61, 67]
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
    · change IsUnit ((2 : ZMod 16349) ^ 8174 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8174 : ZMod 16349)
      decide
    · change IsUnit ((2 : ZMod 16349) ^ 8174 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8174 : ZMod 16349)
      decide
    · change IsUnit ((2 : ZMod 16349) ^ 268 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14761 : ZMod 16349)
      decide
    · change IsUnit ((2 : ZMod 16349) ^ 244 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9546 : ZMod 16349)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16361 : Nat.Prime 16361 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16361 16360 1 3 [2, 2, 2, 5, 409]
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
    · change IsUnit ((3 : ZMod 16361) ^ 8180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8180 : ZMod 16361)
      decide
    · change IsUnit ((3 : ZMod 16361) ^ 8180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8180 : ZMod 16361)
      decide
    · change IsUnit ((3 : ZMod 16361) ^ 8180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8180 : ZMod 16361)
      decide
    · change IsUnit ((3 : ZMod 16361) ^ 3272 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1618 : ZMod 16361)
      decide
    · change IsUnit ((3 : ZMod 16361) ^ 40 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10344 : ZMod 16361)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16363 : Nat.Prime 16363 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16363 16362 1 2 [2, 3, 3, 3, 3, 101]
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
    · change IsUnit ((2 : ZMod 16363) ^ 8181 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8181 : ZMod 16363)
      decide
    · change IsUnit ((2 : ZMod 16363) ^ 5454 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14396 : ZMod 16363)
      decide
    · change IsUnit ((2 : ZMod 16363) ^ 5454 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14396 : ZMod 16363)
      decide
    · change IsUnit ((2 : ZMod 16363) ^ 5454 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14396 : ZMod 16363)
      decide
    · change IsUnit ((2 : ZMod 16363) ^ 5454 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14396 : ZMod 16363)
      decide
    · change IsUnit ((2 : ZMod 16363) ^ 162 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16018 : ZMod 16363)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16369 : Nat.Prime 16369 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16369 16368 1 7 [2, 2, 2, 2, 3, 11, 31]
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
    · change IsUnit ((7 : ZMod 16369) ^ 8184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8184 : ZMod 16369)
      decide
    · change IsUnit ((7 : ZMod 16369) ^ 8184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8184 : ZMod 16369)
      decide
    · change IsUnit ((7 : ZMod 16369) ^ 8184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8184 : ZMod 16369)
      decide
    · change IsUnit ((7 : ZMod 16369) ^ 8184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8184 : ZMod 16369)
      decide
    · change IsUnit ((7 : ZMod 16369) ^ 5456 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5343 : ZMod 16369)
      decide
    · change IsUnit ((7 : ZMod 16369) ^ 1488 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11983 : ZMod 16369)
      decide
    · change IsUnit ((7 : ZMod 16369) ^ 528 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4497 : ZMod 16369)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16381 : Nat.Prime 16381 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16381 16380 1 2 [2, 2, 3, 3, 5, 7, 13]
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
    · change IsUnit ((2 : ZMod 16381) ^ 8190 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8190 : ZMod 16381)
      decide
    · change IsUnit ((2 : ZMod 16381) ^ 8190 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8190 : ZMod 16381)
      decide
    · change IsUnit ((2 : ZMod 16381) ^ 5460 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9789 : ZMod 16381)
      decide
    · change IsUnit ((2 : ZMod 16381) ^ 5460 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9789 : ZMod 16381)
      decide
    · change IsUnit ((2 : ZMod 16381) ^ 3276 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6241 : ZMod 16381)
      decide
    · change IsUnit ((2 : ZMod 16381) ^ 2340 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14329 : ZMod 16381)
      decide
    · change IsUnit ((2 : ZMod 16381) ^ 1260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5786 : ZMod 16381)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16411 : Nat.Prime 16411 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16411 16410 1 3 [2, 3, 5, 547]
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
    · change IsUnit ((3 : ZMod 16411) ^ 8205 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8205 : ZMod 16411)
      decide
    · change IsUnit ((3 : ZMod 16411) ^ 5470 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11859 : ZMod 16411)
      decide
    · change IsUnit ((3 : ZMod 16411) ^ 3282 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2569 : ZMod 16411)
      decide
    · change IsUnit ((3 : ZMod 16411) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16311 : ZMod 16411)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16319) (q := 16333) (by exact lowPrime_16333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16333) (q := 16339) (by exact lowPrime_16339) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16339) (q := 16349) (by exact lowPrime_16349) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16349) (q := 16361) (by exact lowPrime_16361) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16361) (q := 16363) (by exact lowPrime_16363) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16363) (q := 16369) (by exact lowPrime_16369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16369) (q := 16381) (by exact lowPrime_16381) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16381) (q := 16411) (by exact lowPrime_16411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part01_chain :
    DusartPrimeRowsChain 16319 16411 dusartPrimeRows_16319_17158_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · apply DusartPrimeRowsChain.empty
                  norm_num
