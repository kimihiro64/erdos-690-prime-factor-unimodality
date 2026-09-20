import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 146 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12959 : Nat.Prime 12959 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12959 12958 1 7 [2, 11, 19, 31]
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
    · apply IsUnit.of_mul_eq_one (6479 : ZMod 12959)
      decide
    · apply IsUnit.of_mul_eq_one (5493 : ZMod 12959)
      decide
    · apply IsUnit.of_mul_eq_one (1943 : ZMod 12959)
      decide
    · apply IsUnit.of_mul_eq_one (5925 : ZMod 12959)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12967 : Nat.Prime 12967 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12967 12966 1 3 [2, 3, 2161]
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
    · apply IsUnit.of_mul_eq_one (6483 : ZMod 12967)
      decide
    · apply IsUnit.of_mul_eq_one (10550 : ZMod 12967)
      decide
    · apply IsUnit.of_mul_eq_one (8140 : ZMod 12967)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12973 : Nat.Prime 12973 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12973 12972 1 14 [2, 2, 3, 23, 47]
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
    · apply IsUnit.of_mul_eq_one (6486 : ZMod 12973)
      decide
    · apply IsUnit.of_mul_eq_one (6286 : ZMod 12973)
      decide
    · apply IsUnit.of_mul_eq_one (6563 : ZMod 12973)
      decide
    · apply IsUnit.of_mul_eq_one (8449 : ZMod 12973)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12979 : Nat.Prime 12979 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12979 12978 1 2 [2, 3, 3, 7, 103]
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
    · apply IsUnit.of_mul_eq_one (6489 : ZMod 12979)
      decide
    · apply IsUnit.of_mul_eq_one (1280 : ZMod 12979)
      decide
    · apply IsUnit.of_mul_eq_one (7548 : ZMod 12979)
      decide
    · apply IsUnit.of_mul_eq_one (12058 : ZMod 12979)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12983 : Nat.Prime 12983 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12983 12982 1 5 [2, 6491]
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
    · apply IsUnit.of_mul_eq_one (6491 : ZMod 12983)
      decide
    · apply IsUnit.of_mul_eq_one (541 : ZMod 12983)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13001 : Nat.Prime 13001 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13001 13000 1 3 [2, 2, 2, 5, 5, 5, 13]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6500 : ZMod 13001)
      decide
    · apply IsUnit.of_mul_eq_one (10677 : ZMod 13001)
      decide
    · apply IsUnit.of_mul_eq_one (9781 : ZMod 13001)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13003 : Nat.Prime 13003 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13003 13002 1 5 [2, 3, 11, 197]
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
    · apply IsUnit.of_mul_eq_one (6501 : ZMod 13003)
      decide
    · apply IsUnit.of_mul_eq_one (562 : ZMod 13003)
      decide
    · apply IsUnit.of_mul_eq_one (1109 : ZMod 13003)
      decide
    · apply IsUnit.of_mul_eq_one (4618 : ZMod 13003)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13007 : Nat.Prime 13007 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13007 13006 1 5 [2, 7, 929]
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
    · apply IsUnit.of_mul_eq_one (6503 : ZMod 13007)
      decide
    · apply IsUnit.of_mul_eq_one (1412 : ZMod 13007)
      decide
    · apply IsUnit.of_mul_eq_one (9066 : ZMod 13007)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12953) (q := 12959) (by exact lowPrime_12959) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12959) (q := 12967) (by exact lowPrime_12967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12967) (q := 12973) (by exact lowPrime_12973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12973) (q := 12979) (by exact lowPrime_12979) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12979) (q := 12983) (by exact lowPrime_12983) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12983) (q := 13001) (by exact lowPrime_13001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13001) (q := 13003) (by exact lowPrime_13003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13003) (q := 13007) (by exact lowPrime_13007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part04_chain :
    DusartPrimeRowsChain 12953 13006 dusartPrimeRows_12713_13366_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_13359]
          · norm_num [dusartPrimeRow_of_explicit_13359]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_13359]
            · norm_num [dusartPrimeRow_of_explicit_13359]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_13359]
              · norm_num [dusartPrimeRow_of_explicit_13359]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_13359]
                · norm_num [dusartPrimeRow_of_explicit_13359]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_13359, dusartPrimeRow_of_explicit_right]
