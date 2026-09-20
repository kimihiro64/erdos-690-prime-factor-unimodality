import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 238 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_20327 : Nat.Prime 20327 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20327 20326 1 5 [2, 10163]
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
    · change IsUnit ((5 : ZMod 20327) ^ 10163 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10163 : ZMod 20327)
      decide
    · change IsUnit ((5 : ZMod 20327) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (847 : ZMod 20327)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20333 : Nat.Prime 20333 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20333 20332 1 3 [2, 2, 13, 17, 23]
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
    · change IsUnit ((3 : ZMod 20333) ^ 10166 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10166 : ZMod 20333)
      decide
    · change IsUnit ((3 : ZMod 20333) ^ 10166 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10166 : ZMod 20333)
      decide
    · change IsUnit ((3 : ZMod 20333) ^ 1564 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2081 : ZMod 20333)
      decide
    · change IsUnit ((3 : ZMod 20333) ^ 1196 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5054 : ZMod 20333)
      decide
    · change IsUnit ((3 : ZMod 20333) ^ 884 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16253 : ZMod 20333)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20341 : Nat.Prime 20341 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20341 20340 1 2 [2, 2, 3, 3, 5, 113]
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
    · change IsUnit ((2 : ZMod 20341) ^ 10170 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10170 : ZMod 20341)
      decide
    · change IsUnit ((2 : ZMod 20341) ^ 10170 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10170 : ZMod 20341)
      decide
    · change IsUnit ((2 : ZMod 20341) ^ 6780 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19555 : ZMod 20341)
      decide
    · change IsUnit ((2 : ZMod 20341) ^ 6780 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19555 : ZMod 20341)
      decide
    · change IsUnit ((2 : ZMod 20341) ^ 4068 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9816 : ZMod 20341)
      decide
    · change IsUnit ((2 : ZMod 20341) ^ 180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8869 : ZMod 20341)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20347 : Nat.Prime 20347 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20347 20346 1 3 [2, 3, 3391]
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
    · change IsUnit ((3 : ZMod 20347) ^ 10173 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10173 : ZMod 20347)
      decide
    · change IsUnit ((3 : ZMod 20347) ^ 6782 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13897 : ZMod 20347)
      decide
    · change IsUnit ((3 : ZMod 20347) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18698 : ZMod 20347)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20353 : Nat.Prime 20353 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20353 20352 1 5 [2, 2, 2, 2, 2, 2, 2, 3, 53]
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
    · change IsUnit ((5 : ZMod 20353) ^ 10176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10176 : ZMod 20353)
      decide
    · change IsUnit ((5 : ZMod 20353) ^ 10176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10176 : ZMod 20353)
      decide
    · change IsUnit ((5 : ZMod 20353) ^ 10176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10176 : ZMod 20353)
      decide
    · change IsUnit ((5 : ZMod 20353) ^ 10176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10176 : ZMod 20353)
      decide
    · change IsUnit ((5 : ZMod 20353) ^ 10176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10176 : ZMod 20353)
      decide
    · change IsUnit ((5 : ZMod 20353) ^ 10176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10176 : ZMod 20353)
      decide
    · change IsUnit ((5 : ZMod 20353) ^ 10176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10176 : ZMod 20353)
      decide
    · change IsUnit ((5 : ZMod 20353) ^ 6784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19058 : ZMod 20353)
      decide
    · change IsUnit ((5 : ZMod 20353) ^ 384 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3547 : ZMod 20353)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20357 : Nat.Prime 20357 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20357 20356 1 2 [2, 2, 7, 727]
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
    · change IsUnit ((2 : ZMod 20357) ^ 10178 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10178 : ZMod 20357)
      decide
    · change IsUnit ((2 : ZMod 20357) ^ 10178 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10178 : ZMod 20357)
      decide
    · change IsUnit ((2 : ZMod 20357) ^ 2908 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (75 : ZMod 20357)
      decide
    · change IsUnit ((2 : ZMod 20357) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17546 : ZMod 20357)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20359 : Nat.Prime 20359 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20359 20358 1 11 [2, 3, 3, 3, 13, 29]
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
    · change IsUnit ((11 : ZMod 20359) ^ 10179 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10179 : ZMod 20359)
      decide
    · change IsUnit ((11 : ZMod 20359) ^ 6786 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9006 : ZMod 20359)
      decide
    · change IsUnit ((11 : ZMod 20359) ^ 6786 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9006 : ZMod 20359)
      decide
    · change IsUnit ((11 : ZMod 20359) ^ 6786 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9006 : ZMod 20359)
      decide
    · change IsUnit ((11 : ZMod 20359) ^ 1566 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2012 : ZMod 20359)
      decide
    · change IsUnit ((11 : ZMod 20359) ^ 702 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11143 : ZMod 20359)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20369 : Nat.Prime 20369 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20369 20368 1 3 [2, 2, 2, 2, 19, 67]
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
    · change IsUnit ((3 : ZMod 20369) ^ 10184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10184 : ZMod 20369)
      decide
    · change IsUnit ((3 : ZMod 20369) ^ 10184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10184 : ZMod 20369)
      decide
    · change IsUnit ((3 : ZMod 20369) ^ 10184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10184 : ZMod 20369)
      decide
    · change IsUnit ((3 : ZMod 20369) ^ 10184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10184 : ZMod 20369)
      decide
    · change IsUnit ((3 : ZMod 20369) ^ 1072 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18587 : ZMod 20369)
      decide
    · change IsUnit ((3 : ZMod 20369) ^ 304 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12271 : ZMod 20369)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20323) (q := 20327) (by exact lowPrime_20327) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20327) (q := 20333) (by exact lowPrime_20333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20333) (q := 20341) (by exact lowPrime_20341) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20341) (q := 20347) (by exact lowPrime_20347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20347) (q := 20353) (by exact lowPrime_20353) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20353) (q := 20357) (by exact lowPrime_20357) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20357) (q := 20359) (by exact lowPrime_20359) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20359) (q := 20369) (by exact lowPrime_20369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part06_chain :
    DusartPrimeRowsChain 20323 20369 dusartPrimeRows_19937_20958_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · apply DusartPrimeRowsChain.empty
                  norm_num
