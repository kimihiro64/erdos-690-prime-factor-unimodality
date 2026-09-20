import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 110 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10343 : Nat.Prime 10343 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10343 10342 1 5 [2, 5171]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (5171 : ZMod 10343)
      decide
    · apply IsUnit.of_mul_eq_one (431 : ZMod 10343)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10357 : Nat.Prime 10357 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10357 10356 1 2 [2, 2, 3, 863]
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
    · apply IsUnit.of_mul_eq_one (5178 : ZMod 10357)
      decide
    · apply IsUnit.of_mul_eq_one (8173 : ZMod 10357)
      decide
    · apply IsUnit.of_mul_eq_one (650 : ZMod 10357)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10369 : Nat.Prime 10369 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10369 10368 1 13 [2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (5184 : ZMod 10369)
      decide
    · apply IsUnit.of_mul_eq_one (3178 : ZMod 10369)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10391 : Nat.Prime 10391 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10391 10390 1 19 [2, 5, 1039]
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
    · apply IsUnit.of_mul_eq_one (5195 : ZMod 10391)
      decide
    · apply IsUnit.of_mul_eq_one (4826 : ZMod 10391)
      decide
    · apply IsUnit.of_mul_eq_one (6067 : ZMod 10391)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10399 : Nat.Prime 10399 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10399 10398 1 6 [2, 3, 1733]
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
    · apply IsUnit.of_mul_eq_one (5199 : ZMod 10399)
      decide
    · apply IsUnit.of_mul_eq_one (3614 : ZMod 10399)
      decide
    · apply IsUnit.of_mul_eq_one (37 : ZMod 10399)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10427 : Nat.Prime 10427 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10427 10426 1 2 [2, 13, 401]
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
    · apply IsUnit.of_mul_eq_one (5213 : ZMod 10427)
      decide
    · apply IsUnit.of_mul_eq_one (6444 : ZMod 10427)
      decide
    · apply IsUnit.of_mul_eq_one (1177 : ZMod 10427)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10337) (q := 10343) (by exact lowPrime_10343) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10343) (q := 10357) (by exact lowPrime_10357) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10357) (q := 10369) (by exact lowPrime_10369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10369) (q := 10391) (by exact lowPrime_10391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10391) (q := 10399) (by exact lowPrime_10399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10399) (q := 10427) (by exact lowPrime_10427) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part07_chain :
    DusartPrimeRowsChain 10337 10426 dusartPrimeRows_9901_10426_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.empty
              norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]
