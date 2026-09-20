import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 137 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_12323 : Nat.Prime 12323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12323 12322 1 2 [2, 61, 101]
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
    · change IsUnit ((2 : ZMod 12323) ^ 6161 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6161 : ZMod 12323)
      decide
    · change IsUnit ((2 : ZMod 12323) ^ 202 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5544 : ZMod 12323)
      decide
    · change IsUnit ((2 : ZMod 12323) ^ 122 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7108 : ZMod 12323)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12329 : Nat.Prime 12329 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12329 12328 1 3 [2, 2, 2, 23, 67]
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
    · change IsUnit ((3 : ZMod 12329) ^ 6164 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6164 : ZMod 12329)
      decide
    · change IsUnit ((3 : ZMod 12329) ^ 6164 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6164 : ZMod 12329)
      decide
    · change IsUnit ((3 : ZMod 12329) ^ 6164 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6164 : ZMod 12329)
      decide
    · change IsUnit ((3 : ZMod 12329) ^ 536 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5546 : ZMod 12329)
      decide
    · change IsUnit ((3 : ZMod 12329) ^ 184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4919 : ZMod 12329)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12343 : Nat.Prime 12343 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12343 12342 1 7 [2, 3, 11, 11, 17]
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
    · change IsUnit ((7 : ZMod 12343) ^ 6171 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6171 : ZMod 12343)
      decide
    · change IsUnit ((7 : ZMod 12343) ^ 4114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2973 : ZMod 12343)
      decide
    · change IsUnit ((7 : ZMod 12343) ^ 1122 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (329 : ZMod 12343)
      decide
    · change IsUnit ((7 : ZMod 12343) ^ 1122 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (329 : ZMod 12343)
      decide
    · change IsUnit ((7 : ZMod 12343) ^ 726 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10564 : ZMod 12343)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12347 : Nat.Prime 12347 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12347 12346 1 2 [2, 6173]
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
    · change IsUnit ((2 : ZMod 12347) ^ 6173 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6173 : ZMod 12347)
      decide
    · change IsUnit ((2 : ZMod 12347) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4116 : ZMod 12347)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12373 : Nat.Prime 12373 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12373 12372 1 2 [2, 2, 3, 1031]
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
    · change IsUnit ((2 : ZMod 12373) ^ 6186 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6186 : ZMod 12373)
      decide
    · change IsUnit ((2 : ZMod 12373) ^ 6186 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6186 : ZMod 12373)
      decide
    · change IsUnit ((2 : ZMod 12373) ^ 4124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3625 : ZMod 12373)
      decide
    · change IsUnit ((2 : ZMod 12373) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2109 : ZMod 12373)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12377 : Nat.Prime 12377 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12377 12376 1 6 [2, 2, 2, 7, 13, 17]
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
    · change IsUnit ((6 : ZMod 12377) ^ 6188 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6188 : ZMod 12377)
      decide
    · change IsUnit ((6 : ZMod 12377) ^ 6188 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6188 : ZMod 12377)
      decide
    · change IsUnit ((6 : ZMod 12377) ^ 6188 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6188 : ZMod 12377)
      decide
    · change IsUnit ((6 : ZMod 12377) ^ 1768 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8825 : ZMod 12377)
      decide
    · change IsUnit ((6 : ZMod 12377) ^ 952 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6991 : ZMod 12377)
      decide
    · change IsUnit ((6 : ZMod 12377) ^ 728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11353 : ZMod 12377)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12379 : Nat.Prime 12379 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12379 12378 1 2 [2, 3, 2063]
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
    · change IsUnit ((2 : ZMod 12379) ^ 6189 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6189 : ZMod 12379)
      decide
    · change IsUnit ((2 : ZMod 12379) ^ 4126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6329 : ZMod 12379)
      decide
    · change IsUnit ((2 : ZMod 12379) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (393 : ZMod 12379)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12391 : Nat.Prime 12391 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12391 12390 1 26 [2, 3, 5, 7, 59]
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
    · change IsUnit ((26 : ZMod 12391) ^ 6195 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6195 : ZMod 12391)
      decide
    · change IsUnit ((26 : ZMod 12391) ^ 4130 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1409 : ZMod 12391)
      decide
    · change IsUnit ((26 : ZMod 12391) ^ 2478 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (953 : ZMod 12391)
      decide
    · change IsUnit ((26 : ZMod 12391) ^ 1770 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (956 : ZMod 12391)
      decide
    · change IsUnit ((26 : ZMod 12391) ^ 210 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8506 : ZMod 12391)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12301) (q := 12323) (by exact lowPrime_12323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12323) (q := 12329) (by exact lowPrime_12329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12329) (q := 12343) (by exact lowPrime_12343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12343) (q := 12347) (by exact lowPrime_12347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12347) (q := 12373) (by exact lowPrime_12373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12373) (q := 12377) (by exact lowPrime_12377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12377) (q := 12379) (by exact lowPrime_12379) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12379) (q := 12391) (by exact lowPrime_12391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part04_chain :
    DusartPrimeRowsChain 12301 12391 dusartPrimeRows_12097_12712_part04 := by
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
