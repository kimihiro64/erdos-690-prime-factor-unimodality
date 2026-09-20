import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 272 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17239 : Nat.Prime 17239 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17239 17238 1 6 [2, 3, 13, 13, 17]
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
    · apply IsUnit.of_mul_eq_one (8619 : ZMod 17239)
      decide
    · apply IsUnit.of_mul_eq_one (12180 : ZMod 17239)
      decide
    · apply IsUnit.of_mul_eq_one (977 : ZMod 17239)
      decide
    · apply IsUnit.of_mul_eq_one (6885 : ZMod 17239)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17257 : Nat.Prime 17257 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17257 17256 1 5 [2, 2, 2, 3, 719]
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
    · apply IsUnit.of_mul_eq_one (8628 : ZMod 17257)
      decide
    · apply IsUnit.of_mul_eq_one (11047 : ZMod 17257)
      decide
    · apply IsUnit.of_mul_eq_one (3177 : ZMod 17257)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17291 : Nat.Prime 17291 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17291 17290 1 6 [2, 5, 7, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (8645 : ZMod 17291)
      decide
    · apply IsUnit.of_mul_eq_one (13376 : ZMod 17291)
      decide
    · apply IsUnit.of_mul_eq_one (8543 : ZMod 17291)
      decide
    · apply IsUnit.of_mul_eq_one (2709 : ZMod 17291)
      decide
    · apply IsUnit.of_mul_eq_one (1176 : ZMod 17291)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17293 : Nat.Prime 17293 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17293 17292 1 7 [2, 2, 3, 11, 131]
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
    · apply IsUnit.of_mul_eq_one (8646 : ZMod 17293)
      decide
    · apply IsUnit.of_mul_eq_one (11572 : ZMod 17293)
      decide
    · apply IsUnit.of_mul_eq_one (16257 : ZMod 17293)
      decide
    · apply IsUnit.of_mul_eq_one (10519 : ZMod 17293)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17299 : Nat.Prime 17299 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17299 17298 1 2 [2, 3, 3, 31, 31]
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
    · apply IsUnit.of_mul_eq_one (8649 : ZMod 17299)
      decide
    · apply IsUnit.of_mul_eq_one (1907 : ZMod 17299)
      decide
    · apply IsUnit.of_mul_eq_one (5345 : ZMod 17299)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17317 : Nat.Prime 17317 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17317 17316 1 2 [2, 2, 3, 3, 13, 37]
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
    · apply IsUnit.of_mul_eq_one (8658 : ZMod 17317)
      decide
    · apply IsUnit.of_mul_eq_one (15177 : ZMod 17317)
      decide
    · apply IsUnit.of_mul_eq_one (13628 : ZMod 17317)
      decide
    · apply IsUnit.of_mul_eq_one (10493 : ZMod 17317)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17321 : Nat.Prime 17321 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17321 17320 1 3 [2, 2, 2, 5, 433]
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
    · apply IsUnit.of_mul_eq_one (8660 : ZMod 17321)
      decide
    · apply IsUnit.of_mul_eq_one (13962 : ZMod 17321)
      decide
    · apply IsUnit.of_mul_eq_one (16914 : ZMod 17321)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17327 : Nat.Prime 17327 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17327 17326 1 5 [2, 8663]
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
    · apply IsUnit.of_mul_eq_one (8663 : ZMod 17327)
      decide
    · apply IsUnit.of_mul_eq_one (722 : ZMod 17327)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17231) (q := 17239) (by exact lowPrime_17239) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17239) (q := 17257) (by exact lowPrime_17257) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17257) (q := 17291) (by exact lowPrime_17291) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17291) (q := 17293) (by exact lowPrime_17293) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17293) (q := 17299) (by exact lowPrime_17299) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17299) (q := 17317) (by exact lowPrime_17317) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17317) (q := 17321) (by exact lowPrime_17321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17321) (q := 17327) (by exact lowPrime_17327) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part02_chain :
    DusartPrimeRowsChain 17231 17326 dusartPrimeRows_17159_18040_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]
