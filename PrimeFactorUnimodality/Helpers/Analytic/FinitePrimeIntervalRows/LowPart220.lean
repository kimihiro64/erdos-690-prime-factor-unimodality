import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 220 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21023 : Nat.Prime 21023 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21023 21022 1 5 [2, 23, 457]
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
    · apply IsUnit.of_mul_eq_one (10511 : ZMod 21023)
      decide
    · apply IsUnit.of_mul_eq_one (18711 : ZMod 21023)
      decide
    · apply IsUnit.of_mul_eq_one (5355 : ZMod 21023)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21031 : Nat.Prime 21031 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21031 21030 1 12 [2, 3, 5, 701]
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
    · apply IsUnit.of_mul_eq_one (10515 : ZMod 21031)
      decide
    · apply IsUnit.of_mul_eq_one (7627 : ZMod 21031)
      decide
    · apply IsUnit.of_mul_eq_one (15934 : ZMod 21031)
      decide
    · apply IsUnit.of_mul_eq_one (16696 : ZMod 21031)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21059 : Nat.Prime 21059 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21059 21058 1 2 [2, 10529]
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
    · apply IsUnit.of_mul_eq_one (10529 : ZMod 21059)
      decide
    · apply IsUnit.of_mul_eq_one (7020 : ZMod 21059)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21061 : Nat.Prime 21061 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21061 21060 1 7 [2, 2, 3, 3, 3, 3, 5, 13]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10530 : ZMod 21061)
      decide
    · apply IsUnit.of_mul_eq_one (12915 : ZMod 21061)
      decide
    · apply IsUnit.of_mul_eq_one (529 : ZMod 21061)
      decide
    · apply IsUnit.of_mul_eq_one (13446 : ZMod 21061)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21067 : Nat.Prime 21067 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21067 21066 1 2 [2, 3, 3511]
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
    · apply IsUnit.of_mul_eq_one (10533 : ZMod 21067)
      decide
    · apply IsUnit.of_mul_eq_one (15271 : ZMod 21067)
      decide
    · apply IsUnit.of_mul_eq_one (1672 : ZMod 21067)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21089 : Nat.Prime 21089 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21089 21088 1 3 [2, 2, 2, 2, 2, 659]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (10544 : ZMod 21089)
      decide
    · apply IsUnit.of_mul_eq_one (8655 : ZMod 21089)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21101 : Nat.Prime 21101 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21101 21100 1 2 [2, 2, 5, 5, 211]
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
    · apply IsUnit.of_mul_eq_one (10550 : ZMod 21101)
      decide
    · apply IsUnit.of_mul_eq_one (2119 : ZMod 21101)
      decide
    · apply IsUnit.of_mul_eq_one (15408 : ZMod 21101)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21107 : Nat.Prime 21107 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21107 21106 1 2 [2, 61, 173]
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
    · apply IsUnit.of_mul_eq_one (10553 : ZMod 21107)
      decide
    · apply IsUnit.of_mul_eq_one (17377 : ZMod 21107)
      decide
    · apply IsUnit.of_mul_eq_one (13322 : ZMod 21107)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21019) (q := 21023) (by exact lowPrime_21023) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21023) (q := 21031) (by exact lowPrime_21031) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21031) (q := 21059) (by exact lowPrime_21059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21059) (q := 21061) (by exact lowPrime_21061) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21061) (q := 21067) (by exact lowPrime_21067) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21067) (q := 21089) (by exact lowPrime_21089) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21089) (q := 21101) (by exact lowPrime_21101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21101) (q := 21107) (by exact lowPrime_21107) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part02_chain :
    DusartPrimeRowsChain 21019 21106 dusartPrimeRows_20959_22026_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]
