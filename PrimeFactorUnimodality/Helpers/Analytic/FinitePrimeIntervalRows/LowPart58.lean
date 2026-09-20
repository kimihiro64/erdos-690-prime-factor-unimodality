import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 58 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6911 : Nat.Prime 6911 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6911 6910 1 7 [2, 5, 691]
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
    · apply IsUnit.of_mul_eq_one (3455 : ZMod 6911)
      decide
    · apply IsUnit.of_mul_eq_one (4248 : ZMod 6911)
      decide
    · apply IsUnit.of_mul_eq_one (3372 : ZMod 6911)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6917 : Nat.Prime 6917 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6917 6916 1 2 [2, 2, 7, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (3458 : ZMod 6917)
      decide
    · apply IsUnit.of_mul_eq_one (3679 : ZMod 6917)
      decide
    · apply IsUnit.of_mul_eq_one (5162 : ZMod 6917)
      decide
    · apply IsUnit.of_mul_eq_one (3633 : ZMod 6917)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6947 : Nat.Prime 6947 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6947 6946 1 2 [2, 23, 151]
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
    · apply IsUnit.of_mul_eq_one (3473 : ZMod 6947)
      decide
    · apply IsUnit.of_mul_eq_one (5825 : ZMod 6947)
      decide
    · apply IsUnit.of_mul_eq_one (4994 : ZMod 6947)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6949 : Nat.Prime 6949 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6949 6948 1 2 [2, 2, 3, 3, 193]
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
    · apply IsUnit.of_mul_eq_one (3474 : ZMod 6949)
      decide
    · apply IsUnit.of_mul_eq_one (6301 : ZMod 6949)
      decide
    · apply IsUnit.of_mul_eq_one (4961 : ZMod 6949)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6959 : Nat.Prime 6959 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6959 6958 1 7 [2, 7, 7, 71]
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
    · apply IsUnit.of_mul_eq_one (3479 : ZMod 6959)
      decide
    · apply IsUnit.of_mul_eq_one (3825 : ZMod 6959)
      decide
    · apply IsUnit.of_mul_eq_one (4115 : ZMod 6959)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6961 : Nat.Prime 6961 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6961 6960 1 13 [2, 2, 2, 2, 3, 5, 29]
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
    · apply IsUnit.of_mul_eq_one (3480 : ZMod 6961)
      decide
    · apply IsUnit.of_mul_eq_one (4471 : ZMod 6961)
      decide
    · apply IsUnit.of_mul_eq_one (640 : ZMod 6961)
      decide
    · apply IsUnit.of_mul_eq_one (749 : ZMod 6961)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6967 : Nat.Prime 6967 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6967 6966 1 5 [2, 3, 3, 3, 3, 43]
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
    · apply IsUnit.of_mul_eq_one (3483 : ZMod 6967)
      decide
    · apply IsUnit.of_mul_eq_one (127 : ZMod 6967)
      decide
    · apply IsUnit.of_mul_eq_one (4605 : ZMod 6967)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6971 : Nat.Prime 6971 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6971 6970 1 2 [2, 5, 17, 41]
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
    · apply IsUnit.of_mul_eq_one (3485 : ZMod 6971)
      decide
    · apply IsUnit.of_mul_eq_one (2715 : ZMod 6971)
      decide
    · apply IsUnit.of_mul_eq_one (5236 : ZMod 6971)
      decide
    · apply IsUnit.of_mul_eq_one (923 : ZMod 6971)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6907) (q := 6911) (by exact lowPrime_6911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6911) (q := 6917) (by exact lowPrime_6917) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6917) (q := 6947) (by exact lowPrime_6947) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6947) (q := 6949) (by exact lowPrime_6949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6949) (q := 6959) (by exact lowPrime_6959) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6959) (q := 6961) (by exact lowPrime_6961) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6961) (q := 6967) (by exact lowPrime_6967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6967) (q := 6971) (by exact lowPrime_6971) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part05_chain :
    DusartPrimeRowsChain 6907 6970 dusartPrimeRows_6637_6976_part05 := by
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
