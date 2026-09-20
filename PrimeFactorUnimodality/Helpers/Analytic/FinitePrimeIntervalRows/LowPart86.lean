import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 86 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8719 : Nat.Prime 8719 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8719 8718 1 3 [2, 3, 1453]
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
    · apply IsUnit.of_mul_eq_one (4359 : ZMod 8719)
      decide
    · apply IsUnit.of_mul_eq_one (7958 : ZMod 8719)
      decide
    · apply IsUnit.of_mul_eq_one (3078 : ZMod 8719)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8731 : Nat.Prime 8731 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8731 8730 1 2 [2, 3, 3, 5, 97]
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
    · apply IsUnit.of_mul_eq_one (4365 : ZMod 8731)
      decide
    · apply IsUnit.of_mul_eq_one (7511 : ZMod 8731)
      decide
    · apply IsUnit.of_mul_eq_one (4101 : ZMod 8731)
      decide
    · apply IsUnit.of_mul_eq_one (7838 : ZMod 8731)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8737 : Nat.Prime 8737 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8737 8736 1 5 [2, 2, 2, 2, 2, 3, 7, 13]
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
    · apply IsUnit.of_mul_eq_one (4368 : ZMod 8737)
      decide
    · apply IsUnit.of_mul_eq_one (5068 : ZMod 8737)
      decide
    · apply IsUnit.of_mul_eq_one (6289 : ZMod 8737)
      decide
    · apply IsUnit.of_mul_eq_one (1583 : ZMod 8737)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8741 : Nat.Prime 8741 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8741 8740 1 2 [2, 2, 5, 19, 23]
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
    · apply IsUnit.of_mul_eq_one (4370 : ZMod 8741)
      decide
    · apply IsUnit.of_mul_eq_one (7350 : ZMod 8741)
      decide
    · apply IsUnit.of_mul_eq_one (538 : ZMod 8741)
      decide
    · apply IsUnit.of_mul_eq_one (8561 : ZMod 8741)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8747 : Nat.Prime 8747 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8747 8746 1 2 [2, 4373]
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
    · apply IsUnit.of_mul_eq_one (4373 : ZMod 8747)
      decide
    · apply IsUnit.of_mul_eq_one (2916 : ZMod 8747)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8753 : Nat.Prime 8753 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8753 8752 1 3 [2, 2, 2, 2, 547]
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
    · apply IsUnit.of_mul_eq_one (4376 : ZMod 8753)
      decide
    · apply IsUnit.of_mul_eq_one (377 : ZMod 8753)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8761 : Nat.Prime 8761 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8761 8760 1 23 [2, 2, 2, 3, 5, 73]
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
    · apply IsUnit.of_mul_eq_one (4380 : ZMod 8761)
      decide
    · apply IsUnit.of_mul_eq_one (2342 : ZMod 8761)
      decide
    · apply IsUnit.of_mul_eq_one (2202 : ZMod 8761)
      decide
    · apply IsUnit.of_mul_eq_one (1258 : ZMod 8761)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8779 : Nat.Prime 8779 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8779 8778 1 11 [2, 3, 7, 11, 19]
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
    · apply IsUnit.of_mul_eq_one (4389 : ZMod 8779)
      decide
    · apply IsUnit.of_mul_eq_one (422 : ZMod 8779)
      decide
    · apply IsUnit.of_mul_eq_one (5532 : ZMod 8779)
      decide
    · apply IsUnit.of_mul_eq_one (6068 : ZMod 8779)
      decide
    · apply IsUnit.of_mul_eq_one (5351 : ZMod 8779)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8713) (q := 8719) (by exact lowPrime_8719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8719) (q := 8731) (by exact lowPrime_8731) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8731) (q := 8737) (by exact lowPrime_8737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8737) (q := 8741) (by exact lowPrime_8741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8741) (q := 8747) (by exact lowPrime_8747) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8747) (q := 8753) (by exact lowPrime_8753) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8753) (q := 8761) (by exact lowPrime_8761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8761) (q := 8779) (by exact lowPrime_8779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part04_chain :
    DusartPrimeRowsChain 8713 8778 dusartPrimeRows_8521_8962_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]
