import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 274 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17393 : Nat.Prime 17393 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17393 17392 1 3 [2, 2, 2, 2, 1087]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (8696 : ZMod 17393)
      decide
    · apply IsUnit.of_mul_eq_one (3770 : ZMod 17393)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17401 : Nat.Prime 17401 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17401 17400 1 11 [2, 2, 2, 3, 5, 5, 29]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (8700 : ZMod 17401)
      decide
    · apply IsUnit.of_mul_eq_one (201 : ZMod 17401)
      decide
    · apply IsUnit.of_mul_eq_one (11290 : ZMod 17401)
      decide
    · apply IsUnit.of_mul_eq_one (4786 : ZMod 17401)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17417 : Nat.Prime 17417 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17417 17416 1 3 [2, 2, 2, 7, 311]
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
    · apply IsUnit.of_mul_eq_one (8708 : ZMod 17417)
      decide
    · apply IsUnit.of_mul_eq_one (14203 : ZMod 17417)
      decide
    · apply IsUnit.of_mul_eq_one (4925 : ZMod 17417)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17419 : Nat.Prime 17419 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17419 17418 1 3 [2, 3, 2903]
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
    · apply IsUnit.of_mul_eq_one (8709 : ZMod 17419)
      decide
    · apply IsUnit.of_mul_eq_one (13842 : ZMod 17419)
      decide
    · apply IsUnit.of_mul_eq_one (6245 : ZMod 17419)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17431 : Nat.Prime 17431 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17431 17430 1 3 [2, 3, 5, 7, 83]
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
    · apply IsUnit.of_mul_eq_one (8715 : ZMod 17431)
      decide
    · apply IsUnit.of_mul_eq_one (4815 : ZMod 17431)
      decide
    · apply IsUnit.of_mul_eq_one (15936 : ZMod 17431)
      decide
    · apply IsUnit.of_mul_eq_one (6648 : ZMod 17431)
      decide
    · apply IsUnit.of_mul_eq_one (1033 : ZMod 17431)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17443 : Nat.Prime 17443 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17443 17442 1 2 [2, 3, 3, 3, 17, 19]
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
    · apply IsUnit.of_mul_eq_one (8721 : ZMod 17443)
      decide
    · apply IsUnit.of_mul_eq_one (3773 : ZMod 17443)
      decide
    · apply IsUnit.of_mul_eq_one (15897 : ZMod 17443)
      decide
    · apply IsUnit.of_mul_eq_one (5659 : ZMod 17443)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17449 : Nat.Prime 17449 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17449 17448 1 14 [2, 2, 2, 3, 727]
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
    · apply IsUnit.of_mul_eq_one (8724 : ZMod 17449)
      decide
    · apply IsUnit.of_mul_eq_one (11900 : ZMod 17449)
      decide
    · apply IsUnit.of_mul_eq_one (10142 : ZMod 17449)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17467 : Nat.Prime 17467 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17467 17466 1 3 [2, 3, 41, 71]
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
    · apply IsUnit.of_mul_eq_one (8733 : ZMod 17467)
      decide
    · apply IsUnit.of_mul_eq_one (9347 : ZMod 17467)
      decide
    · apply IsUnit.of_mul_eq_one (1064 : ZMod 17467)
      decide
    · apply IsUnit.of_mul_eq_one (1228 : ZMod 17467)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17389) (q := 17393) (by exact lowPrime_17393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17393) (q := 17401) (by exact lowPrime_17401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17401) (q := 17417) (by exact lowPrime_17417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17417) (q := 17419) (by exact lowPrime_17419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17419) (q := 17431) (by exact lowPrime_17431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17431) (q := 17443) (by exact lowPrime_17443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17443) (q := 17449) (by exact lowPrime_17449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17449) (q := 17467) (by exact lowPrime_17467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part04_chain :
    DusartPrimeRowsChain 17389 17466 dusartPrimeRows_17159_18040_part04 := by
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
