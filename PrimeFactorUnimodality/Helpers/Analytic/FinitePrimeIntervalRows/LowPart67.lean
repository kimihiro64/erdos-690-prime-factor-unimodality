import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 67 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7517 : Nat.Prime 7517 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7517 7516 1 2 [2, 2, 1879]
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
    · apply IsUnit.of_mul_eq_one (3758 : ZMod 7517)
      decide
    · apply IsUnit.of_mul_eq_one (3508 : ZMod 7517)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7523 : Nat.Prime 7523 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7523 7522 1 2 [2, 3761]
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
    · apply IsUnit.of_mul_eq_one (3761 : ZMod 7523)
      decide
    · apply IsUnit.of_mul_eq_one (2508 : ZMod 7523)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7529 : Nat.Prime 7529 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7529 7528 1 3 [2, 2, 2, 941]
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
    · apply IsUnit.of_mul_eq_one (3764 : ZMod 7529)
      decide
    · apply IsUnit.of_mul_eq_one (2836 : ZMod 7529)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7537 : Nat.Prime 7537 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7537 7536 1 7 [2, 2, 2, 2, 3, 157]
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
    · apply IsUnit.of_mul_eq_one (3768 : ZMod 7537)
      decide
    · apply IsUnit.of_mul_eq_one (4370 : ZMod 7537)
      decide
    · apply IsUnit.of_mul_eq_one (4862 : ZMod 7537)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7541 : Nat.Prime 7541 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7541 7540 1 2 [2, 2, 5, 13, 29]
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
    · apply IsUnit.of_mul_eq_one (3770 : ZMod 7541)
      decide
    · apply IsUnit.of_mul_eq_one (5508 : ZMod 7541)
      decide
    · apply IsUnit.of_mul_eq_one (227 : ZMod 7541)
      decide
    · apply IsUnit.of_mul_eq_one (6838 : ZMod 7541)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7547 : Nat.Prime 7547 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7547 7546 1 2 [2, 7, 7, 7, 11]
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
    · apply IsUnit.of_mul_eq_one (3773 : ZMod 7547)
      decide
    · apply IsUnit.of_mul_eq_one (7341 : ZMod 7547)
      decide
    · apply IsUnit.of_mul_eq_one (5352 : ZMod 7547)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7549 : Nat.Prime 7549 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7549 7548 1 2 [2, 2, 3, 17, 37]
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
    · apply IsUnit.of_mul_eq_one (3774 : ZMod 7549)
      decide
    · apply IsUnit.of_mul_eq_one (4856 : ZMod 7549)
      decide
    · apply IsUnit.of_mul_eq_one (2349 : ZMod 7549)
      decide
    · apply IsUnit.of_mul_eq_one (580 : ZMod 7549)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7559 : Nat.Prime 7559 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7559 7558 1 13 [2, 3779]
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
    · apply IsUnit.of_mul_eq_one (3779 : ZMod 7559)
      decide
    · apply IsUnit.of_mul_eq_one (45 : ZMod 7559)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7507) (q := 7517) (by exact lowPrime_7517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7517) (q := 7523) (by exact lowPrime_7523) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7523) (q := 7529) (by exact lowPrime_7529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7529) (q := 7537) (by exact lowPrime_7537) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7537) (q := 7541) (by exact lowPrime_7541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7541) (q := 7547) (by exact lowPrime_7547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7547) (q := 7549) (by exact lowPrime_7549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7549) (q := 7559) (by exact lowPrime_7559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part03_chain :
    DusartPrimeRowsChain 7507 7558 dusartPrimeRows_7333_7716_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_7707, dusartPrimeRow_of_explicit_right]
