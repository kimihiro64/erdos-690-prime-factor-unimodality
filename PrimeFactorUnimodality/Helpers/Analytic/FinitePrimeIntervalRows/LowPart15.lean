import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 15 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_4139 : Nat.Prime 4139 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4139 4138 1 2 [2, 2069]
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
    · change IsUnit ((2 : ZMod 4139) ^ 2069 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2069 : ZMod 4139)
      decide
    · change IsUnit ((2 : ZMod 4139) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1380 : ZMod 4139)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4153 : Nat.Prime 4153 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4153 4152 1 5 [2, 2, 2, 3, 173]
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
    · change IsUnit ((5 : ZMod 4153) ^ 2076 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2076 : ZMod 4153)
      decide
    · change IsUnit ((5 : ZMod 4153) ^ 2076 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2076 : ZMod 4153)
      decide
    · change IsUnit ((5 : ZMod 4153) ^ 2076 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2076 : ZMod 4153)
      decide
    · change IsUnit ((5 : ZMod 4153) ^ 1384 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2825 : ZMod 4153)
      decide
    · change IsUnit ((5 : ZMod 4153) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3154 : ZMod 4153)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4157 : Nat.Prime 4157 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4157 4156 1 2 [2, 2, 1039]
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
    · change IsUnit ((2 : ZMod 4157) ^ 2078 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2078 : ZMod 4157)
      decide
    · change IsUnit ((2 : ZMod 4157) ^ 2078 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2078 : ZMod 4157)
      decide
    · change IsUnit ((2 : ZMod 4157) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1940 : ZMod 4157)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4159 : Nat.Prime 4159 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4159 4158 1 3 [2, 3, 3, 3, 7, 11]
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
    · change IsUnit ((3 : ZMod 4159) ^ 2079 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2079 : ZMod 4159)
      decide
    · change IsUnit ((3 : ZMod 4159) ^ 1386 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (851 : ZMod 4159)
      decide
    · change IsUnit ((3 : ZMod 4159) ^ 1386 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (851 : ZMod 4159)
      decide
    · change IsUnit ((3 : ZMod 4159) ^ 1386 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (851 : ZMod 4159)
      decide
    · change IsUnit ((3 : ZMod 4159) ^ 594 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1837 : ZMod 4159)
      decide
    · change IsUnit ((3 : ZMod 4159) ^ 378 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3046 : ZMod 4159)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4177 : Nat.Prime 4177 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4177 4176 1 5 [2, 2, 2, 2, 3, 3, 29]
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
    · change IsUnit ((5 : ZMod 4177) ^ 2088 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2088 : ZMod 4177)
      decide
    · change IsUnit ((5 : ZMod 4177) ^ 2088 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2088 : ZMod 4177)
      decide
    · change IsUnit ((5 : ZMod 4177) ^ 2088 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2088 : ZMod 4177)
      decide
    · change IsUnit ((5 : ZMod 4177) ^ 2088 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2088 : ZMod 4177)
      decide
    · change IsUnit ((5 : ZMod 4177) ^ 1392 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (367 : ZMod 4177)
      decide
    · change IsUnit ((5 : ZMod 4177) ^ 1392 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (367 : ZMod 4177)
      decide
    · change IsUnit ((5 : ZMod 4177) ^ 144 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1785 : ZMod 4177)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4201 : Nat.Prime 4201 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4201 4200 1 11 [2, 2, 2, 3, 5, 5, 7]
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
    · change IsUnit ((11 : ZMod 4201) ^ 2100 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2100 : ZMod 4201)
      decide
    · change IsUnit ((11 : ZMod 4201) ^ 2100 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2100 : ZMod 4201)
      decide
    · change IsUnit ((11 : ZMod 4201) ^ 2100 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2100 : ZMod 4201)
      decide
    · change IsUnit ((11 : ZMod 4201) ^ 1400 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3175 : ZMod 4201)
      decide
    · change IsUnit ((11 : ZMod 4201) ^ 840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2375 : ZMod 4201)
      decide
    · change IsUnit ((11 : ZMod 4201) ^ 840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2375 : ZMod 4201)
      decide
    · change IsUnit ((11 : ZMod 4201) ^ 600 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1806 : ZMod 4201)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4211 : Nat.Prime 4211 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4211 4210 1 6 [2, 5, 421]
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
    · change IsUnit ((6 : ZMod 4211) ^ 2105 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2105 : ZMod 4211)
      decide
    · change IsUnit ((6 : ZMod 4211) ^ 842 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2746 : ZMod 4211)
      decide
    · change IsUnit ((6 : ZMod 4211) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3094 : ZMod 4211)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4217 : Nat.Prime 4217 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4217 4216 1 3 [2, 2, 2, 17, 31]
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
    · change IsUnit ((3 : ZMod 4217) ^ 2108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2108 : ZMod 4217)
      decide
    · change IsUnit ((3 : ZMod 4217) ^ 2108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2108 : ZMod 4217)
      decide
    · change IsUnit ((3 : ZMod 4217) ^ 2108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2108 : ZMod 4217)
      decide
    · change IsUnit ((3 : ZMod 4217) ^ 248 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3291 : ZMod 4217)
      decide
    · change IsUnit ((3 : ZMod 4217) ^ 136 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3244 : ZMod 4217)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4133) (q := 4139) (by exact lowPrime_4139) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4139) (q := 4153) (by exact lowPrime_4153) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4153) (q := 4157) (by exact lowPrime_4157) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4157) (q := 4159) (by exact lowPrime_4159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4159) (q := 4177) (by exact lowPrime_4177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4177) (q := 4201) (by exact lowPrime_4201) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4201) (q := 4211) (by exact lowPrime_4211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4211) (q := 4217) (by exact lowPrime_4217) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part06_chain :
    DusartPrimeRowsChain 4133 4217 dusartPrimeRows_3803_4672_part06 := by
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
