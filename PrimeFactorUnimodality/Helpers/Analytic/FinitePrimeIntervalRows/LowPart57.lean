import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 57 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6841 : Nat.Prime 6841 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6841 6840 1 22 [2, 2, 2, 3, 3, 5, 19]
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
    · apply IsUnit.of_mul_eq_one (3420 : ZMod 6841)
      decide
    · apply IsUnit.of_mul_eq_one (3624 : ZMod 6841)
      decide
    · apply IsUnit.of_mul_eq_one (3423 : ZMod 6841)
      decide
    · apply IsUnit.of_mul_eq_one (4003 : ZMod 6841)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6857 : Nat.Prime 6857 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6857 6856 1 3 [2, 2, 2, 857]
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
    · apply IsUnit.of_mul_eq_one (3428 : ZMod 6857)
      decide
    · apply IsUnit.of_mul_eq_one (1847 : ZMod 6857)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6863 : Nat.Prime 6863 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6863 6862 1 5 [2, 47, 73]
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
    · apply IsUnit.of_mul_eq_one (3431 : ZMod 6863)
      decide
    · apply IsUnit.of_mul_eq_one (382 : ZMod 6863)
      decide
    · apply IsUnit.of_mul_eq_one (4422 : ZMod 6863)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6869 : Nat.Prime 6869 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6869 6868 1 2 [2, 2, 17, 101]
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
    · apply IsUnit.of_mul_eq_one (3434 : ZMod 6869)
      decide
    · apply IsUnit.of_mul_eq_one (572 : ZMod 6869)
      decide
    · apply IsUnit.of_mul_eq_one (3734 : ZMod 6869)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6871 : Nat.Prime 6871 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6871 6870 1 3 [2, 3, 5, 229]
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
    · apply IsUnit.of_mul_eq_one (3435 : ZMod 6871)
      decide
    · apply IsUnit.of_mul_eq_one (1801 : ZMod 6871)
      decide
    · apply IsUnit.of_mul_eq_one (3908 : ZMod 6871)
      decide
    · apply IsUnit.of_mul_eq_one (411 : ZMod 6871)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6883 : Nat.Prime 6883 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6883 6882 1 2 [2, 3, 31, 37]
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
    · apply IsUnit.of_mul_eq_one (3441 : ZMod 6883)
      decide
    · apply IsUnit.of_mul_eq_one (2367 : ZMod 6883)
      decide
    · apply IsUnit.of_mul_eq_one (1683 : ZMod 6883)
      decide
    · apply IsUnit.of_mul_eq_one (6021 : ZMod 6883)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6899 : Nat.Prime 6899 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6899 6898 1 2 [2, 3449]
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
    · apply IsUnit.of_mul_eq_one (3449 : ZMod 6899)
      decide
    · apply IsUnit.of_mul_eq_one (2300 : ZMod 6899)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6907 : Nat.Prime 6907 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6907 6906 1 2 [2, 3, 1151]
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
    · apply IsUnit.of_mul_eq_one (3453 : ZMod 6907)
      decide
    · apply IsUnit.of_mul_eq_one (5223 : ZMod 6907)
      decide
    · apply IsUnit.of_mul_eq_one (1206 : ZMod 6907)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6833) (q := 6841) (by exact lowPrime_6841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6841) (q := 6857) (by exact lowPrime_6857) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6857) (q := 6863) (by exact lowPrime_6863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6863) (q := 6869) (by exact lowPrime_6869) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6869) (q := 6871) (by exact lowPrime_6871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6871) (q := 6883) (by exact lowPrime_6883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6883) (q := 6899) (by exact lowPrime_6899) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6899) (q := 6907) (by exact lowPrime_6907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part04_chain :
    DusartPrimeRowsChain 6833 6906 dusartPrimeRows_6637_6976_part04 := by
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
