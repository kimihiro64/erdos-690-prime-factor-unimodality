import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 263 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_18311 : Nat.Prime 18311 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18311 18310 1 13 [2, 5, 1831]
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
    · change IsUnit ((13 : ZMod 18311) ^ 9155 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9155 : ZMod 18311)
      decide
    · change IsUnit ((13 : ZMod 18311) ^ 3662 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2654 : ZMod 18311)
      decide
    · change IsUnit ((13 : ZMod 18311) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3709 : ZMod 18311)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18313 : Nat.Prime 18313 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18313 18312 1 10 [2, 2, 2, 3, 7, 109]
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
    · change IsUnit ((10 : ZMod 18313) ^ 9156 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9156 : ZMod 18313)
      decide
    · change IsUnit ((10 : ZMod 18313) ^ 9156 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9156 : ZMod 18313)
      decide
    · change IsUnit ((10 : ZMod 18313) ^ 9156 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9156 : ZMod 18313)
      decide
    · change IsUnit ((10 : ZMod 18313) ^ 6104 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (997 : ZMod 18313)
      decide
    · change IsUnit ((10 : ZMod 18313) ^ 2616 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9675 : ZMod 18313)
      decide
    · change IsUnit ((10 : ZMod 18313) ^ 168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2521 : ZMod 18313)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18329 : Nat.Prime 18329 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18329 18328 1 3 [2, 2, 2, 29, 79]
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
    · change IsUnit ((3 : ZMod 18329) ^ 9164 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9164 : ZMod 18329)
      decide
    · change IsUnit ((3 : ZMod 18329) ^ 9164 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9164 : ZMod 18329)
      decide
    · change IsUnit ((3 : ZMod 18329) ^ 9164 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9164 : ZMod 18329)
      decide
    · change IsUnit ((3 : ZMod 18329) ^ 632 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11378 : ZMod 18329)
      decide
    · change IsUnit ((3 : ZMod 18329) ^ 232 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9344 : ZMod 18329)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18341 : Nat.Prime 18341 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18341 18340 1 3 [2, 2, 5, 7, 131]
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
    · change IsUnit ((3 : ZMod 18341) ^ 9170 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9170 : ZMod 18341)
      decide
    · change IsUnit ((3 : ZMod 18341) ^ 9170 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9170 : ZMod 18341)
      decide
    · change IsUnit ((3 : ZMod 18341) ^ 3668 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10579 : ZMod 18341)
      decide
    · change IsUnit ((3 : ZMod 18341) ^ 2620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12998 : ZMod 18341)
      decide
    · change IsUnit ((3 : ZMod 18341) ^ 140 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4363 : ZMod 18341)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18353 : Nat.Prime 18353 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18353 18352 1 3 [2, 2, 2, 2, 31, 37]
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
    · change IsUnit ((3 : ZMod 18353) ^ 9176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9176 : ZMod 18353)
      decide
    · change IsUnit ((3 : ZMod 18353) ^ 9176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9176 : ZMod 18353)
      decide
    · change IsUnit ((3 : ZMod 18353) ^ 9176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9176 : ZMod 18353)
      decide
    · change IsUnit ((3 : ZMod 18353) ^ 9176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9176 : ZMod 18353)
      decide
    · change IsUnit ((3 : ZMod 18353) ^ 592 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8481 : ZMod 18353)
      decide
    · change IsUnit ((3 : ZMod 18353) ^ 496 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5670 : ZMod 18353)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18367 : Nat.Prime 18367 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18367 18366 1 3 [2, 3, 3061]
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
    · change IsUnit ((3 : ZMod 18367) ^ 9183 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9183 : ZMod 18367)
      decide
    · change IsUnit ((3 : ZMod 18367) ^ 6122 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4066 : ZMod 18367)
      decide
    · change IsUnit ((3 : ZMod 18367) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11328 : ZMod 18367)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18371 : Nat.Prime 18371 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18371 18370 1 11 [2, 5, 11, 167]
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
    · change IsUnit ((11 : ZMod 18371) ^ 9185 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9185 : ZMod 18371)
      decide
    · change IsUnit ((11 : ZMod 18371) ^ 3674 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8990 : ZMod 18371)
      decide
    · change IsUnit ((11 : ZMod 18371) ^ 1670 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17496 : ZMod 18371)
      decide
    · change IsUnit ((11 : ZMod 18371) ^ 110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11524 : ZMod 18371)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18379 : Nat.Prime 18379 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18379 18378 1 3 [2, 3, 3, 1021]
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
    · change IsUnit ((3 : ZMod 18379) ^ 9189 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9189 : ZMod 18379)
      decide
    · change IsUnit ((3 : ZMod 18379) ^ 6126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15937 : ZMod 18379)
      decide
    · change IsUnit ((3 : ZMod 18379) ^ 6126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15937 : ZMod 18379)
      decide
    · change IsUnit ((3 : ZMod 18379) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3136 : ZMod 18379)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18307) (q := 18311) (by exact lowPrime_18311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18311) (q := 18313) (by exact lowPrime_18313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18313) (q := 18329) (by exact lowPrime_18329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18329) (q := 18341) (by exact lowPrime_18341) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18341) (q := 18353) (by exact lowPrime_18353) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18353) (q := 18367) (by exact lowPrime_18367) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18367) (q := 18371) (by exact lowPrime_18371) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18371) (q := 18379) (by exact lowPrime_18379) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part05_chain :
    DusartPrimeRowsChain 18307 18379 dusartPrimeRows_18041_18958_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num
