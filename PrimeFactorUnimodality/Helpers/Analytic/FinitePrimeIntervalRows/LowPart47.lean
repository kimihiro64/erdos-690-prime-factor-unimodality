import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 47 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_6217 : Nat.Prime 6217 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6217 6216 1 5 [2, 2, 2, 3, 7, 37]
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
    · change IsUnit ((5 : ZMod 6217) ^ 3108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3108 : ZMod 6217)
      decide
    · change IsUnit ((5 : ZMod 6217) ^ 3108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3108 : ZMod 6217)
      decide
    · change IsUnit ((5 : ZMod 6217) ^ 3108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3108 : ZMod 6217)
      decide
    · change IsUnit ((5 : ZMod 6217) ^ 2072 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4964 : ZMod 6217)
      decide
    · change IsUnit ((5 : ZMod 6217) ^ 888 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (859 : ZMod 6217)
      decide
    · change IsUnit ((5 : ZMod 6217) ^ 168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2409 : ZMod 6217)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6221 : Nat.Prime 6221 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6221 6220 1 3 [2, 2, 5, 311]
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
    · change IsUnit ((3 : ZMod 6221) ^ 3110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3110 : ZMod 6221)
      decide
    · change IsUnit ((3 : ZMod 6221) ^ 3110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3110 : ZMod 6221)
      decide
    · change IsUnit ((3 : ZMod 6221) ^ 1244 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2722 : ZMod 6221)
      decide
    · change IsUnit ((3 : ZMod 6221) ^ 20 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1646 : ZMod 6221)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6229 : Nat.Prime 6229 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6229 6228 1 2 [2, 2, 3, 3, 173]
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
    · change IsUnit ((2 : ZMod 6229) ^ 3114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3114 : ZMod 6229)
      decide
    · change IsUnit ((2 : ZMod 6229) ^ 3114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3114 : ZMod 6229)
      decide
    · change IsUnit ((2 : ZMod 6229) ^ 2076 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2386 : ZMod 6229)
      decide
    · change IsUnit ((2 : ZMod 6229) ^ 2076 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2386 : ZMod 6229)
      decide
    · change IsUnit ((2 : ZMod 6229) ^ 36 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (290 : ZMod 6229)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6247 : Nat.Prime 6247 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6247 6246 1 5 [2, 3, 3, 347]
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
    · change IsUnit ((5 : ZMod 6247) ^ 3123 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3123 : ZMod 6247)
      decide
    · change IsUnit ((5 : ZMod 6247) ^ 2082 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3392 : ZMod 6247)
      decide
    · change IsUnit ((5 : ZMod 6247) ^ 2082 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3392 : ZMod 6247)
      decide
    · change IsUnit ((5 : ZMod 6247) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5952 : ZMod 6247)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6257 : Nat.Prime 6257 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6257 6256 1 3 [2, 2, 2, 2, 17, 23]
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
    · change IsUnit ((3 : ZMod 6257) ^ 3128 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3128 : ZMod 6257)
      decide
    · change IsUnit ((3 : ZMod 6257) ^ 3128 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3128 : ZMod 6257)
      decide
    · change IsUnit ((3 : ZMod 6257) ^ 3128 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3128 : ZMod 6257)
      decide
    · change IsUnit ((3 : ZMod 6257) ^ 3128 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3128 : ZMod 6257)
      decide
    · change IsUnit ((3 : ZMod 6257) ^ 368 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4929 : ZMod 6257)
      decide
    · change IsUnit ((3 : ZMod 6257) ^ 272 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (419 : ZMod 6257)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6263 : Nat.Prime 6263 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6263 6262 1 5 [2, 31, 101]
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
    · change IsUnit ((5 : ZMod 6263) ^ 3131 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3131 : ZMod 6263)
      decide
    · change IsUnit ((5 : ZMod 6263) ^ 202 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2109 : ZMod 6263)
      decide
    · change IsUnit ((5 : ZMod 6263) ^ 62 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (295 : ZMod 6263)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6269 : Nat.Prime 6269 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6269 6268 1 2 [2, 2, 1567]
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
    · change IsUnit ((2 : ZMod 6269) ^ 3134 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3134 : ZMod 6269)
      decide
    · change IsUnit ((2 : ZMod 6269) ^ 3134 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3134 : ZMod 6269)
      decide
    · change IsUnit ((2 : ZMod 6269) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (418 : ZMod 6269)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6271 : Nat.Prime 6271 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6271 6270 1 11 [2, 3, 5, 11, 19]
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
    · change IsUnit ((11 : ZMod 6271) ^ 3135 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3135 : ZMod 6271)
      decide
    · change IsUnit ((11 : ZMod 6271) ^ 2090 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5597 : ZMod 6271)
      decide
    · change IsUnit ((11 : ZMod 6271) ^ 1254 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (844 : ZMod 6271)
      decide
    · change IsUnit ((11 : ZMod 6271) ^ 570 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2881 : ZMod 6271)
      decide
    · change IsUnit ((11 : ZMod 6271) ^ 330 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4652 : ZMod 6271)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6211) (q := 6217) (by exact lowPrime_6217) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6217) (q := 6221) (by exact lowPrime_6221) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6221) (q := 6229) (by exact lowPrime_6229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6229) (q := 6247) (by exact lowPrime_6247) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6247) (q := 6257) (by exact lowPrime_6257) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6257) (q := 6263) (by exact lowPrime_6263) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6263) (q := 6269) (by exact lowPrime_6269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6269) (q := 6271) (by exact lowPrime_6271) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part04_chain :
    DusartPrimeRowsChain 6211 6271 dusartPrimeRows_6007_6310_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · apply DusartPrimeRowsChain.empty
                  norm_num
