import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 144 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12809 : Nat.Prime 12809 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12809 12808 1 3 [2, 2, 2, 1601]
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
    · apply IsUnit.of_mul_eq_one (6404 : ZMod 12809)
      decide
    · apply IsUnit.of_mul_eq_one (7949 : ZMod 12809)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12821 : Nat.Prime 12821 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12821 12820 1 2 [2, 2, 5, 641]
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
    · apply IsUnit.of_mul_eq_one (6410 : ZMod 12821)
      decide
    · apply IsUnit.of_mul_eq_one (10098 : ZMod 12821)
      decide
    · apply IsUnit.of_mul_eq_one (2567 : ZMod 12821)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12823 : Nat.Prime 12823 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12823 12822 1 3 [2, 3, 2137]
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
    · apply IsUnit.of_mul_eq_one (6411 : ZMod 12823)
      decide
    · apply IsUnit.of_mul_eq_one (9012 : ZMod 12823)
      decide
    · apply IsUnit.of_mul_eq_one (1004 : ZMod 12823)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12829 : Nat.Prime 12829 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12829 12828 1 2 [2, 2, 3, 1069]
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
    · apply IsUnit.of_mul_eq_one (6414 : ZMod 12829)
      decide
    · apply IsUnit.of_mul_eq_one (7996 : ZMod 12829)
      decide
    · apply IsUnit.of_mul_eq_one (2995 : ZMod 12829)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12841 : Nat.Prime 12841 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12841 12840 1 21 [2, 2, 2, 3, 5, 107]
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
    · apply IsUnit.of_mul_eq_one (6420 : ZMod 12841)
      decide
    · apply IsUnit.of_mul_eq_one (1917 : ZMod 12841)
      decide
    · apply IsUnit.of_mul_eq_one (9998 : ZMod 12841)
      decide
    · apply IsUnit.of_mul_eq_one (10763 : ZMod 12841)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12853 : Nat.Prime 12853 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12853 12852 1 5 [2, 2, 3, 3, 3, 7, 17]
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
    · apply IsUnit.of_mul_eq_one (6426 : ZMod 12853)
      decide
    · apply IsUnit.of_mul_eq_one (6544 : ZMod 12853)
      decide
    · apply IsUnit.of_mul_eq_one (5835 : ZMod 12853)
      decide
    · apply IsUnit.of_mul_eq_one (1482 : ZMod 12853)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12889 : Nat.Prime 12889 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12889 12888 1 13 [2, 2, 2, 3, 3, 179]
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
    · apply IsUnit.of_mul_eq_one (6444 : ZMod 12889)
      decide
    · apply IsUnit.of_mul_eq_one (1419 : ZMod 12889)
      decide
    · apply IsUnit.of_mul_eq_one (11563 : ZMod 12889)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12893 : Nat.Prime 12893 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12893 12892 1 3 [2, 2, 11, 293]
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
    · apply IsUnit.of_mul_eq_one (6446 : ZMod 12893)
      decide
    · apply IsUnit.of_mul_eq_one (7505 : ZMod 12893)
      decide
    · apply IsUnit.of_mul_eq_one (12725 : ZMod 12893)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12799) (q := 12809) (by exact lowPrime_12809) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12809) (q := 12821) (by exact lowPrime_12821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12821) (q := 12823) (by exact lowPrime_12823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12823) (q := 12829) (by exact lowPrime_12829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12829) (q := 12841) (by exact lowPrime_12841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12841) (q := 12853) (by exact lowPrime_12853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12853) (q := 12889) (by exact lowPrime_12889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12889) (q := 12893) (by exact lowPrime_12893) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part02_chain :
    DusartPrimeRowsChain 12799 12892 dusartPrimeRows_12713_13366_part02 := by
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
