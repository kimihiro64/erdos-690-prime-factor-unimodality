import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 51 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6451 : Nat.Prime 6451 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6451 6450 1 3 [2, 3, 5, 5, 43]
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
    · apply IsUnit.of_mul_eq_one (3225 : ZMod 6451)
      decide
    · apply IsUnit.of_mul_eq_one (2079 : ZMod 6451)
      decide
    · apply IsUnit.of_mul_eq_one (2381 : ZMod 6451)
      decide
    · apply IsUnit.of_mul_eq_one (4976 : ZMod 6451)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6469 : Nat.Prime 6469 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6469 6468 1 2 [2, 2, 3, 7, 7, 11]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3234 : ZMod 6469)
      decide
    · apply IsUnit.of_mul_eq_one (2648 : ZMod 6469)
      decide
    · apply IsUnit.of_mul_eq_one (2440 : ZMod 6469)
      decide
    · apply IsUnit.of_mul_eq_one (4342 : ZMod 6469)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6473 : Nat.Prime 6473 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6473 6472 1 3 [2, 2, 2, 809]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (3236 : ZMod 6473)
      decide
    · apply IsUnit.of_mul_eq_one (6101 : ZMod 6473)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6481 : Nat.Prime 6481 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6481 6480 1 7 [2, 2, 2, 2, 3, 3, 3, 3, 5]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3240 : ZMod 6481)
      decide
    · apply IsUnit.of_mul_eq_one (2133 : ZMod 6481)
      decide
    · apply IsUnit.of_mul_eq_one (1195 : ZMod 6481)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6491 : Nat.Prime 6491 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6491 6490 1 2 [2, 5, 11, 59]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3245 : ZMod 6491)
      decide
    · apply IsUnit.of_mul_eq_one (963 : ZMod 6491)
      decide
    · apply IsUnit.of_mul_eq_one (1063 : ZMod 6491)
      decide
    · apply IsUnit.of_mul_eq_one (5417 : ZMod 6491)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6521 : Nat.Prime 6521 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6521 6520 1 6 [2, 2, 2, 5, 163]
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
    · apply IsUnit.of_mul_eq_one (3260 : ZMod 6521)
      decide
    · apply IsUnit.of_mul_eq_one (3465 : ZMod 6521)
      decide
    · apply IsUnit.of_mul_eq_one (3708 : ZMod 6521)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6529 : Nat.Prime 6529 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6529 6528 1 7 [2, 2, 2, 2, 2, 2, 2, 3, 17]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3264 : ZMod 6529)
      decide
    · apply IsUnit.of_mul_eq_one (4516 : ZMod 6529)
      decide
    · apply IsUnit.of_mul_eq_one (1450 : ZMod 6529)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6547 : Nat.Prime 6547 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6547 6546 1 2 [2, 3, 1091]
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
    · apply IsUnit.of_mul_eq_one (3273 : ZMod 6547)
      decide
    · apply IsUnit.of_mul_eq_one (777 : ZMod 6547)
      decide
    · apply IsUnit.of_mul_eq_one (3949 : ZMod 6547)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6449) (q := 6451) (by exact lowPrime_6451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6451) (q := 6469) (by exact lowPrime_6469) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6469) (q := 6473) (by exact lowPrime_6473) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6473) (q := 6481) (by exact lowPrime_6481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6481) (q := 6491) (by exact lowPrime_6491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6491) (q := 6521) (by exact lowPrime_6521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6521) (q := 6529) (by exact lowPrime_6529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6529) (q := 6547) (by exact lowPrime_6547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part03_chain :
    DusartPrimeRowsChain 6449 6546 dusartPrimeRows_6311_6636_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6634]
        · norm_num [dusartPrimeRow_of_explicit_6634]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6634]
          · norm_num [dusartPrimeRow_of_explicit_6634]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6634]
            · norm_num [dusartPrimeRow_of_explicit_6634]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6634]
              · norm_num [dusartPrimeRow_of_explicit_6634]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6634]
                · norm_num [dusartPrimeRow_of_explicit_6634]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6634, dusartPrimeRow_of_explicit_right]
