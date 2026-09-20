import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 19 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4423 : Nat.Prime 4423 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4423 4422 1 3 [2, 3, 11, 67]
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
    · apply IsUnit.of_mul_eq_one (2211 : ZMod 4423)
      decide
    · apply IsUnit.of_mul_eq_one (2926 : ZMod 4423)
      decide
    · apply IsUnit.of_mul_eq_one (2632 : ZMod 4423)
      decide
    · apply IsUnit.of_mul_eq_one (2174 : ZMod 4423)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4441 : Nat.Prime 4441 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4441 4440 1 21 [2, 2, 2, 3, 5, 37]
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
    · apply IsUnit.of_mul_eq_one (2220 : ZMod 4441)
      decide
    · apply IsUnit.of_mul_eq_one (300 : ZMod 4441)
      decide
    · apply IsUnit.of_mul_eq_one (3489 : ZMod 4441)
      decide
    · apply IsUnit.of_mul_eq_one (289 : ZMod 4441)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4447 : Nat.Prime 4447 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4447 4446 1 3 [2, 3, 3, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (2223 : ZMod 4447)
      decide
    · apply IsUnit.of_mul_eq_one (4408 : ZMod 4447)
      decide
    · apply IsUnit.of_mul_eq_one (827 : ZMod 4447)
      decide
    · apply IsUnit.of_mul_eq_one (3754 : ZMod 4447)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4451 : Nat.Prime 4451 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4451 4450 1 2 [2, 5, 5, 89]
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
    · apply IsUnit.of_mul_eq_one (2225 : ZMod 4451)
      decide
    · apply IsUnit.of_mul_eq_one (3476 : ZMod 4451)
      decide
    · apply IsUnit.of_mul_eq_one (2301 : ZMod 4451)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4457 : Nat.Prime 4457 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4457 4456 1 3 [2, 2, 2, 557]
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
    · apply IsUnit.of_mul_eq_one (2228 : ZMod 4457)
      decide
    · apply IsUnit.of_mul_eq_one (657 : ZMod 4457)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4463 : Nat.Prime 4463 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4463 4462 1 5 [2, 23, 97]
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
    · apply IsUnit.of_mul_eq_one (2231 : ZMod 4463)
      decide
    · apply IsUnit.of_mul_eq_one (3102 : ZMod 4463)
      decide
    · apply IsUnit.of_mul_eq_one (2557 : ZMod 4463)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4481 : Nat.Prime 4481 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4481 4480 1 3 [2, 2, 2, 2, 2, 2, 2, 5, 7]
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
    · apply IsUnit.of_mul_eq_one (2240 : ZMod 4481)
      decide
    · apply IsUnit.of_mul_eq_one (917 : ZMod 4481)
      decide
    · apply IsUnit.of_mul_eq_one (4450 : ZMod 4481)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4483 : Nat.Prime 4483 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4483 4482 1 2 [2, 3, 3, 3, 83]
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
    · apply IsUnit.of_mul_eq_one (2241 : ZMod 4483)
      decide
    · apply IsUnit.of_mul_eq_one (4314 : ZMod 4483)
      decide
    · apply IsUnit.of_mul_eq_one (2394 : ZMod 4483)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4421) (q := 4423) (by exact lowPrime_4423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4423) (q := 4441) (by exact lowPrime_4441) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4441) (q := 4447) (by exact lowPrime_4447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4447) (q := 4451) (by exact lowPrime_4451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4451) (q := 4457) (by exact lowPrime_4457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4457) (q := 4463) (by exact lowPrime_4463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4463) (q := 4481) (by exact lowPrime_4481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4481) (q := 4483) (by exact lowPrime_4483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part10_chain :
    DusartPrimeRowsChain 4421 4482 dusartPrimeRows_3803_4672_part10 := by
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
