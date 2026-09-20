import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 93 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9187 : Nat.Prime 9187 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9187 9186 1 3 [2, 3, 1531]
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
    · apply IsUnit.of_mul_eq_one (4593 : ZMod 9187)
      decide
    · apply IsUnit.of_mul_eq_one (1688 : ZMod 9187)
      decide
    · apply IsUnit.of_mul_eq_one (2587 : ZMod 9187)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9199 : Nat.Prime 9199 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9199 9198 1 3 [2, 3, 3, 7, 73]
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
    · apply IsUnit.of_mul_eq_one (4599 : ZMod 9199)
      decide
    · apply IsUnit.of_mul_eq_one (7388 : ZMod 9199)
      decide
    · apply IsUnit.of_mul_eq_one (6854 : ZMod 9199)
      decide
    · apply IsUnit.of_mul_eq_one (4952 : ZMod 9199)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9203 : Nat.Prime 9203 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9203 9202 1 2 [2, 43, 107]
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
    · apply IsUnit.of_mul_eq_one (4601 : ZMod 9203)
      decide
    · apply IsUnit.of_mul_eq_one (823 : ZMod 9203)
      decide
    · apply IsUnit.of_mul_eq_one (8760 : ZMod 9203)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9209 : Nat.Prime 9209 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9209 9208 1 3 [2, 2, 2, 1151]
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
    · apply IsUnit.of_mul_eq_one (4604 : ZMod 9209)
      decide
    · apply IsUnit.of_mul_eq_one (5378 : ZMod 9209)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9221 : Nat.Prime 9221 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9221 9220 1 2 [2, 2, 5, 461]
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
    · apply IsUnit.of_mul_eq_one (4610 : ZMod 9221)
      decide
    · apply IsUnit.of_mul_eq_one (3946 : ZMod 9221)
      decide
    · apply IsUnit.of_mul_eq_one (6091 : ZMod 9221)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9227 : Nat.Prime 9227 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9227 9226 1 2 [2, 7, 659]
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
    · apply IsUnit.of_mul_eq_one (4613 : ZMod 9227)
      decide
    · apply IsUnit.of_mul_eq_one (8015 : ZMod 9227)
      decide
    · apply IsUnit.of_mul_eq_one (3591 : ZMod 9227)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9239 : Nat.Prime 9239 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9239 9238 1 19 [2, 31, 149]
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
    · apply IsUnit.of_mul_eq_one (4619 : ZMod 9239)
      decide
    · apply IsUnit.of_mul_eq_one (8339 : ZMod 9239)
      decide
    · apply IsUnit.of_mul_eq_one (2649 : ZMod 9239)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9241 : Nat.Prime 9241 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9241 9240 1 13 [2, 2, 2, 3, 5, 7, 11]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4620 : ZMod 9241)
      decide
    · apply IsUnit.of_mul_eq_one (55 : ZMod 9241)
      decide
    · apply IsUnit.of_mul_eq_one (3810 : ZMod 9241)
      decide
    · apply IsUnit.of_mul_eq_one (7833 : ZMod 9241)
      decide
    · apply IsUnit.of_mul_eq_one (4937 : ZMod 9241)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9181) (q := 9187) (by exact lowPrime_9187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9187) (q := 9199) (by exact lowPrime_9199) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9199) (q := 9203) (by exact lowPrime_9203) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9203) (q := 9209) (by exact lowPrime_9209) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9209) (q := 9221) (by exact lowPrime_9221) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9221) (q := 9227) (by exact lowPrime_9227) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9227) (q := 9239) (by exact lowPrime_9239) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9239) (q := 9241) (by exact lowPrime_9241) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part04_chain :
    DusartPrimeRowsChain 9181 9240 dusartPrimeRows_8963_9418_part04 := by
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
