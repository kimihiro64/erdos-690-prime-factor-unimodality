import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 54 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6653 : Nat.Prime 6653 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6653 6652 1 2 [2, 2, 1663]
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
    · apply IsUnit.of_mul_eq_one (3326 : ZMod 6653)
      decide
    · apply IsUnit.of_mul_eq_one (5766 : ZMod 6653)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6659 : Nat.Prime 6659 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6659 6658 1 2 [2, 3329]
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
    · apply IsUnit.of_mul_eq_one (3329 : ZMod 6659)
      decide
    · apply IsUnit.of_mul_eq_one (2220 : ZMod 6659)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6661 : Nat.Prime 6661 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6661 6660 1 6 [2, 2, 3, 3, 5, 37]
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
    · apply IsUnit.of_mul_eq_one (3330 : ZMod 6661)
      decide
    · apply IsUnit.of_mul_eq_one (449 : ZMod 6661)
      decide
    · apply IsUnit.of_mul_eq_one (2784 : ZMod 6661)
      decide
    · apply IsUnit.of_mul_eq_one (4999 : ZMod 6661)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6673 : Nat.Prime 6673 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6673 6672 1 5 [2, 2, 2, 2, 3, 139]
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
    · apply IsUnit.of_mul_eq_one (3336 : ZMod 6673)
      decide
    · apply IsUnit.of_mul_eq_one (464 : ZMod 6673)
      decide
    · apply IsUnit.of_mul_eq_one (6387 : ZMod 6673)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6679 : Nat.Prime 6679 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6679 6678 1 7 [2, 3, 3, 7, 53]
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
    · apply IsUnit.of_mul_eq_one (3339 : ZMod 6679)
      decide
    · apply IsUnit.of_mul_eq_one (4138 : ZMod 6679)
      decide
    · apply IsUnit.of_mul_eq_one (705 : ZMod 6679)
      decide
    · apply IsUnit.of_mul_eq_one (5402 : ZMod 6679)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6689 : Nat.Prime 6689 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6689 6688 1 3 [2, 2, 2, 2, 2, 11, 19]
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
    · apply IsUnit.of_mul_eq_one (3344 : ZMod 6689)
      decide
    · apply IsUnit.of_mul_eq_one (2711 : ZMod 6689)
      decide
    · apply IsUnit.of_mul_eq_one (4069 : ZMod 6689)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6691 : Nat.Prime 6691 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6691 6690 1 2 [2, 3, 5, 223]
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
    · apply IsUnit.of_mul_eq_one (3345 : ZMod 6691)
      decide
    · apply IsUnit.of_mul_eq_one (5433 : ZMod 6691)
      decide
    · apply IsUnit.of_mul_eq_one (3847 : ZMod 6691)
      decide
    · apply IsUnit.of_mul_eq_one (106 : ZMod 6691)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6701 : Nat.Prime 6701 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6701 6700 1 2 [2, 2, 5, 5, 67]
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
    · apply IsUnit.of_mul_eq_one (3350 : ZMod 6701)
      decide
    · apply IsUnit.of_mul_eq_one (4052 : ZMod 6701)
      decide
    · apply IsUnit.of_mul_eq_one (2296 : ZMod 6701)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6637) (q := 6653) (by exact lowPrime_6653) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6653) (q := 6659) (by exact lowPrime_6659) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6659) (q := 6661) (by exact lowPrime_6661) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6661) (q := 6673) (by exact lowPrime_6673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6673) (q := 6679) (by exact lowPrime_6679) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6679) (q := 6689) (by exact lowPrime_6689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6689) (q := 6691) (by exact lowPrime_6691) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6691) (q := 6701) (by exact lowPrime_6701) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part01_chain :
    DusartPrimeRowsChain 6637 6700 dusartPrimeRows_6637_6976_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6974]
    · norm_num [dusartPrimeRow_of_explicit_6974]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6974]
      · norm_num [dusartPrimeRow_of_explicit_6974]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6974]
        · norm_num [dusartPrimeRow_of_explicit_6974]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6974]
          · norm_num [dusartPrimeRow_of_explicit_6974]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6974]
            · norm_num [dusartPrimeRow_of_explicit_6974]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6974]
              · norm_num [dusartPrimeRow_of_explicit_6974]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6974]
                · norm_num [dusartPrimeRow_of_explicit_6974]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6974, dusartPrimeRow_of_explicit_right]
