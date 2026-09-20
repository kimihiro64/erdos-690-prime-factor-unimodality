import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 18 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4349 : Nat.Prime 4349 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4349 4348 1 2 [2, 2, 1087]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (2174 : ZMod 4349)
      decide
    · apply IsUnit.of_mul_eq_one (290 : ZMod 4349)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4357 : Nat.Prime 4357 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4357 4356 1 2 [2, 2, 3, 3, 11, 11]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2178 : ZMod 4357)
      decide
    · apply IsUnit.of_mul_eq_one (3917 : ZMod 4357)
      decide
    · apply IsUnit.of_mul_eq_one (3605 : ZMod 4357)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4363 : Nat.Prime 4363 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4363 4362 1 2 [2, 3, 727]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2181 : ZMod 4363)
      decide
    · apply IsUnit.of_mul_eq_one (4225 : ZMod 4363)
      decide
    · apply IsUnit.of_mul_eq_one (4086 : ZMod 4363)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4373 : Nat.Prime 4373 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4373 4372 1 2 [2, 2, 1093]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (2186 : ZMod 4373)
      decide
    · apply IsUnit.of_mul_eq_one (3790 : ZMod 4373)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4391 : Nat.Prime 4391 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4391 4390 1 14 [2, 5, 439]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2195 : ZMod 4391)
      decide
    · apply IsUnit.of_mul_eq_one (4358 : ZMod 4391)
      decide
    · apply IsUnit.of_mul_eq_one (552 : ZMod 4391)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4397 : Nat.Prime 4397 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4397 4396 1 2 [2, 2, 7, 157]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2198 : ZMod 4397)
      decide
    · apply IsUnit.of_mul_eq_one (1321 : ZMod 4397)
      decide
    · apply IsUnit.of_mul_eq_one (1680 : ZMod 4397)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4409 : Nat.Prime 4409 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4409 4408 1 3 [2, 2, 2, 19, 29]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2204 : ZMod 4409)
      decide
    · apply IsUnit.of_mul_eq_one (1505 : ZMod 4409)
      decide
    · apply IsUnit.of_mul_eq_one (3656 : ZMod 4409)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4421 : Nat.Prime 4421 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4421 4420 1 3 [2, 2, 5, 13, 17]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2210 : ZMod 4421)
      decide
    · apply IsUnit.of_mul_eq_one (280 : ZMod 4421)
      decide
    · apply IsUnit.of_mul_eq_one (1950 : ZMod 4421)
      decide
    · apply IsUnit.of_mul_eq_one (3615 : ZMod 4421)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4339) (q := 4349) (by exact lowPrime_4349) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4349) (q := 4357) (by exact lowPrime_4357) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4357) (q := 4363) (by exact lowPrime_4363) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4363) (q := 4373) (by exact lowPrime_4373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4373) (q := 4391) (by exact lowPrime_4391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4391) (q := 4397) (by exact lowPrime_4397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4397) (q := 4409) (by exact lowPrime_4409) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4409) (q := 4421) (by exact lowPrime_4421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part09_chain :
    DusartPrimeRowsChain 4339 4420 dusartPrimeRows_3803_4672_part09 := by
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
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]
