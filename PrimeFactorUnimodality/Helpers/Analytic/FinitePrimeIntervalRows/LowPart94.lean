import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 94 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9257 : Nat.Prime 9257 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9257 9256 1 3 [2, 2, 2, 13, 89]
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
    · apply IsUnit.of_mul_eq_one (4628 : ZMod 9257)
      decide
    · apply IsUnit.of_mul_eq_one (9089 : ZMod 9257)
      decide
    · apply IsUnit.of_mul_eq_one (2232 : ZMod 9257)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9277 : Nat.Prime 9277 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9277 9276 1 5 [2, 2, 3, 773]
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
    · apply IsUnit.of_mul_eq_one (4638 : ZMod 9277)
      decide
    · apply IsUnit.of_mul_eq_one (200 : ZMod 9277)
      decide
    · apply IsUnit.of_mul_eq_one (501 : ZMod 9277)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9281 : Nat.Prime 9281 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9281 9280 1 3 [2, 2, 2, 2, 2, 2, 5, 29]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4640 : ZMod 9281)
      decide
    · apply IsUnit.of_mul_eq_one (5274 : ZMod 9281)
      decide
    · apply IsUnit.of_mul_eq_one (2969 : ZMod 9281)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9283 : Nat.Prime 9283 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9283 9282 1 2 [2, 3, 7, 13, 17]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4641 : ZMod 9283)
      decide
    · apply IsUnit.of_mul_eq_one (7136 : ZMod 9283)
      decide
    · apply IsUnit.of_mul_eq_one (668 : ZMod 9283)
      decide
    · apply IsUnit.of_mul_eq_one (1880 : ZMod 9283)
      decide
    · apply IsUnit.of_mul_eq_one (5129 : ZMod 9283)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9293 : Nat.Prime 9293 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9293 9292 1 2 [2, 2, 23, 101]
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
    · apply IsUnit.of_mul_eq_one (4646 : ZMod 9293)
      decide
    · apply IsUnit.of_mul_eq_one (7818 : ZMod 9293)
      decide
    · apply IsUnit.of_mul_eq_one (9230 : ZMod 9293)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9311 : Nat.Prime 9311 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9311 9310 1 7 [2, 5, 7, 7, 19]
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
    · apply IsUnit.of_mul_eq_one (4655 : ZMod 9311)
      decide
    · apply IsUnit.of_mul_eq_one (2945 : ZMod 9311)
      decide
    · apply IsUnit.of_mul_eq_one (780 : ZMod 9311)
      decide
    · apply IsUnit.of_mul_eq_one (6720 : ZMod 9311)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9319 : Nat.Prime 9319 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9319 9318 1 3 [2, 3, 1553]
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
    · apply IsUnit.of_mul_eq_one (4659 : ZMod 9319)
      decide
    · apply IsUnit.of_mul_eq_one (5166 : ZMod 9319)
      decide
    · apply IsUnit.of_mul_eq_one (3085 : ZMod 9319)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9323 : Nat.Prime 9323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9323 9322 1 2 [2, 59, 79]
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
    · apply IsUnit.of_mul_eq_one (4661 : ZMod 9323)
      decide
    · apply IsUnit.of_mul_eq_one (330 : ZMod 9323)
      decide
    · apply IsUnit.of_mul_eq_one (5173 : ZMod 9323)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9241) (q := 9257) (by exact lowPrime_9257) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9257) (q := 9277) (by exact lowPrime_9277) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9277) (q := 9281) (by exact lowPrime_9281) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9281) (q := 9283) (by exact lowPrime_9283) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9283) (q := 9293) (by exact lowPrime_9293) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9293) (q := 9311) (by exact lowPrime_9311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9311) (q := 9319) (by exact lowPrime_9319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9319) (q := 9323) (by exact lowPrime_9323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part05_chain :
    DusartPrimeRowsChain 9241 9322 dusartPrimeRows_8963_9418_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9414, dusartPrimeRow_of_explicit_right]
