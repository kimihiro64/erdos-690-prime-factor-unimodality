import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 217 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_23041 : Nat.Prime 23041 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23041 23040 1 11 [2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 5]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((11 : ZMod 23041) ^ 11520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11520 : ZMod 23041)
      decide
    · change IsUnit ((11 : ZMod 23041) ^ 11520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11520 : ZMod 23041)
      decide
    · change IsUnit ((11 : ZMod 23041) ^ 11520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11520 : ZMod 23041)
      decide
    · change IsUnit ((11 : ZMod 23041) ^ 11520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11520 : ZMod 23041)
      decide
    · change IsUnit ((11 : ZMod 23041) ^ 11520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11520 : ZMod 23041)
      decide
    · change IsUnit ((11 : ZMod 23041) ^ 11520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11520 : ZMod 23041)
      decide
    · change IsUnit ((11 : ZMod 23041) ^ 11520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11520 : ZMod 23041)
      decide
    · change IsUnit ((11 : ZMod 23041) ^ 11520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11520 : ZMod 23041)
      decide
    · change IsUnit ((11 : ZMod 23041) ^ 11520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11520 : ZMod 23041)
      decide
    · change IsUnit ((11 : ZMod 23041) ^ 7680 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1360 : ZMod 23041)
      decide
    · change IsUnit ((11 : ZMod 23041) ^ 7680 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1360 : ZMod 23041)
      decide
    · change IsUnit ((11 : ZMod 23041) ^ 4608 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15797 : ZMod 23041)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_23053 : Nat.Prime 23053 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23053 23052 1 2 [2, 2, 3, 17, 113]
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
    · change IsUnit ((2 : ZMod 23053) ^ 11526 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11526 : ZMod 23053)
      decide
    · change IsUnit ((2 : ZMod 23053) ^ 11526 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11526 : ZMod 23053)
      decide
    · change IsUnit ((2 : ZMod 23053) ^ 7684 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1033 : ZMod 23053)
      decide
    · change IsUnit ((2 : ZMod 23053) ^ 1356 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11285 : ZMod 23053)
      decide
    · change IsUnit ((2 : ZMod 23053) ^ 204 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7904 : ZMod 23053)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_23057 : Nat.Prime 23057 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23057 23056 1 5 [2, 2, 2, 2, 11, 131]
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
    · change IsUnit ((5 : ZMod 23057) ^ 11528 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11528 : ZMod 23057)
      decide
    · change IsUnit ((5 : ZMod 23057) ^ 11528 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11528 : ZMod 23057)
      decide
    · change IsUnit ((5 : ZMod 23057) ^ 11528 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11528 : ZMod 23057)
      decide
    · change IsUnit ((5 : ZMod 23057) ^ 11528 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11528 : ZMod 23057)
      decide
    · change IsUnit ((5 : ZMod 23057) ^ 2096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4427 : ZMod 23057)
      decide
    · change IsUnit ((5 : ZMod 23057) ^ 176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14769 : ZMod 23057)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_23059 : Nat.Prime 23059 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23059 23058 1 3 [2, 3, 3, 3, 7, 61]
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
    · change IsUnit ((3 : ZMod 23059) ^ 11529 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11529 : ZMod 23059)
      decide
    · change IsUnit ((3 : ZMod 23059) ^ 7686 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3645 : ZMod 23059)
      decide
    · change IsUnit ((3 : ZMod 23059) ^ 7686 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3645 : ZMod 23059)
      decide
    · change IsUnit ((3 : ZMod 23059) ^ 7686 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3645 : ZMod 23059)
      decide
    · change IsUnit ((3 : ZMod 23059) ^ 3294 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16323 : ZMod 23059)
      decide
    · change IsUnit ((3 : ZMod 23059) ^ 378 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11565 : ZMod 23059)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_23063 : Nat.Prime 23063 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23063 23062 1 5 [2, 13, 887]
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
    · change IsUnit ((5 : ZMod 23063) ^ 11531 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11531 : ZMod 23063)
      decide
    · change IsUnit ((5 : ZMod 23063) ^ 1774 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6926 : ZMod 23063)
      decide
    · change IsUnit ((5 : ZMod 23063) ^ 26 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18685 : ZMod 23063)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_23071 : Nat.Prime 23071 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23071 23070 1 3 [2, 3, 5, 769]
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
    · change IsUnit ((3 : ZMod 23071) ^ 11535 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11535 : ZMod 23071)
      decide
    · change IsUnit ((3 : ZMod 23071) ^ 7690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6944 : ZMod 23071)
      decide
    · change IsUnit ((3 : ZMod 23071) ^ 4614 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7634 : ZMod 23071)
      decide
    · change IsUnit ((3 : ZMod 23071) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11219 : ZMod 23071)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_23081 : Nat.Prime 23081 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23081 23080 1 3 [2, 2, 2, 5, 577]
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
    · change IsUnit ((3 : ZMod 23081) ^ 11540 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11540 : ZMod 23081)
      decide
    · change IsUnit ((3 : ZMod 23081) ^ 11540 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11540 : ZMod 23081)
      decide
    · change IsUnit ((3 : ZMod 23081) ^ 11540 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11540 : ZMod 23081)
      decide
    · change IsUnit ((3 : ZMod 23081) ^ 4616 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9804 : ZMod 23081)
      decide
    · change IsUnit ((3 : ZMod 23081) ^ 40 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16919 : ZMod 23081)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_23087 : Nat.Prime 23087 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23087 23086 1 5 [2, 7, 17, 97]
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
    · change IsUnit ((5 : ZMod 23087) ^ 11543 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11543 : ZMod 23087)
      decide
    · change IsUnit ((5 : ZMod 23087) ^ 3298 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12677 : ZMod 23087)
      decide
    · change IsUnit ((5 : ZMod 23087) ^ 1358 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16477 : ZMod 23087)
      decide
    · change IsUnit ((5 : ZMod 23087) ^ 238 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10451 : ZMod 23087)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part14 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 23039) (q := 23041) (by exact lowPrime_23041) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23041) (q := 23053) (by exact lowPrime_23053) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23053) (q := 23057) (by exact lowPrime_23057) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23057) (q := 23059) (by exact lowPrime_23059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23059) (q := 23063) (by exact lowPrime_23063) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23063) (q := 23071) (by exact lowPrime_23071) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23071) (q := 23081) (by exact lowPrime_23081) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23081) (q := 23087) (by exact lowPrime_23087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part14_chain :
    DusartPrimeRowsChain 23039 23087 dusartPrimeRows_22027_23158_part14 := by
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
