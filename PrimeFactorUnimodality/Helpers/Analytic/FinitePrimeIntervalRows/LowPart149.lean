import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 149 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_13171 : Nat.Prime 13171 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13171 13170 1 11 [2, 3, 5, 439]
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
    · change IsUnit ((11 : ZMod 13171) ^ 6585 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6585 : ZMod 13171)
      decide
    · change IsUnit ((11 : ZMod 13171) ^ 4390 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11215 : ZMod 13171)
      decide
    · change IsUnit ((11 : ZMod 13171) ^ 2634 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (302 : ZMod 13171)
      decide
    · change IsUnit ((11 : ZMod 13171) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8691 : ZMod 13171)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13177 : Nat.Prime 13177 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13177 13176 1 5 [2, 2, 2, 3, 3, 3, 61]
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
    · change IsUnit ((5 : ZMod 13177) ^ 6588 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6588 : ZMod 13177)
      decide
    · change IsUnit ((5 : ZMod 13177) ^ 6588 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6588 : ZMod 13177)
      decide
    · change IsUnit ((5 : ZMod 13177) ^ 6588 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6588 : ZMod 13177)
      decide
    · change IsUnit ((5 : ZMod 13177) ^ 4392 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9790 : ZMod 13177)
      decide
    · change IsUnit ((5 : ZMod 13177) ^ 4392 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9790 : ZMod 13177)
      decide
    · change IsUnit ((5 : ZMod 13177) ^ 4392 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9790 : ZMod 13177)
      decide
    · change IsUnit ((5 : ZMod 13177) ^ 216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4466 : ZMod 13177)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13183 : Nat.Prime 13183 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13183 13182 1 3 [2, 3, 13, 13, 13]
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
    · change IsUnit ((3 : ZMod 13183) ^ 6591 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6591 : ZMod 13183)
      decide
    · change IsUnit ((3 : ZMod 13183) ^ 4394 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4973 : ZMod 13183)
      decide
    · change IsUnit ((3 : ZMod 13183) ^ 1014 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2299 : ZMod 13183)
      decide
    · change IsUnit ((3 : ZMod 13183) ^ 1014 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2299 : ZMod 13183)
      decide
    · change IsUnit ((3 : ZMod 13183) ^ 1014 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2299 : ZMod 13183)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13187 : Nat.Prime 13187 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13187 13186 1 2 [2, 19, 347]
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
    · change IsUnit ((2 : ZMod 13187) ^ 6593 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6593 : ZMod 13187)
      decide
    · change IsUnit ((2 : ZMod 13187) ^ 694 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6384 : ZMod 13187)
      decide
    · change IsUnit ((2 : ZMod 13187) ^ 38 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7007 : ZMod 13187)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13217 : Nat.Prime 13217 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13217 13216 1 3 [2, 2, 2, 2, 2, 7, 59]
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
    · change IsUnit ((3 : ZMod 13217) ^ 6608 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6608 : ZMod 13217)
      decide
    · change IsUnit ((3 : ZMod 13217) ^ 6608 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6608 : ZMod 13217)
      decide
    · change IsUnit ((3 : ZMod 13217) ^ 6608 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6608 : ZMod 13217)
      decide
    · change IsUnit ((3 : ZMod 13217) ^ 6608 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6608 : ZMod 13217)
      decide
    · change IsUnit ((3 : ZMod 13217) ^ 6608 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6608 : ZMod 13217)
      decide
    · change IsUnit ((3 : ZMod 13217) ^ 1888 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3824 : ZMod 13217)
      decide
    · change IsUnit ((3 : ZMod 13217) ^ 224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6257 : ZMod 13217)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13219 : Nat.Prime 13219 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13219 13218 1 3 [2, 3, 2203]
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
    · change IsUnit ((3 : ZMod 13219) ^ 6609 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6609 : ZMod 13219)
      decide
    · change IsUnit ((3 : ZMod 13219) ^ 4406 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6904 : ZMod 13219)
      decide
    · change IsUnit ((3 : ZMod 13219) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12874 : ZMod 13219)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13229 : Nat.Prime 13229 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13229 13228 1 2 [2, 2, 3307]
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
    · change IsUnit ((2 : ZMod 13229) ^ 6614 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6614 : ZMod 13229)
      decide
    · change IsUnit ((2 : ZMod 13229) ^ 6614 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6614 : ZMod 13229)
      decide
    · change IsUnit ((2 : ZMod 13229) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (882 : ZMod 13229)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13241 : Nat.Prime 13241 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13241 13240 1 3 [2, 2, 2, 5, 331]
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
    · change IsUnit ((3 : ZMod 13241) ^ 6620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6620 : ZMod 13241)
      decide
    · change IsUnit ((3 : ZMod 13241) ^ 6620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6620 : ZMod 13241)
      decide
    · change IsUnit ((3 : ZMod 13241) ^ 6620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6620 : ZMod 13241)
      decide
    · change IsUnit ((3 : ZMod 13241) ^ 2648 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (779 : ZMod 13241)
      decide
    · change IsUnit ((3 : ZMod 13241) ^ 40 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4678 : ZMod 13241)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13163) (q := 13171) (by exact lowPrime_13171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13171) (q := 13177) (by exact lowPrime_13177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13177) (q := 13183) (by exact lowPrime_13183) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13183) (q := 13187) (by exact lowPrime_13187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13187) (q := 13217) (by exact lowPrime_13217) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13217) (q := 13219) (by exact lowPrime_13219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13219) (q := 13229) (by exact lowPrime_13229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13229) (q := 13241) (by exact lowPrime_13241) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part07_chain :
    DusartPrimeRowsChain 13163 13241 dusartPrimeRows_12713_13366_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_13359]
          · norm_num [dusartPrimeRow_of_explicit_13359]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_13359]
            · norm_num [dusartPrimeRow_of_explicit_13359]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_13359]
              · norm_num [dusartPrimeRow_of_explicit_13359]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_13359]
                · norm_num [dusartPrimeRow_of_explicit_13359]
                · apply DusartPrimeRowsChain.empty
                  norm_num
