import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 55 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6703 : Nat.Prime 6703 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6703 6702 1 5 [2, 3, 1117]
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
    · apply IsUnit.of_mul_eq_one (3351 : ZMod 6703)
      decide
    · apply IsUnit.of_mul_eq_one (6209 : ZMod 6703)
      decide
    · apply IsUnit.of_mul_eq_one (4651 : ZMod 6703)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6709 : Nat.Prime 6709 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6709 6708 1 2 [2, 2, 3, 13, 43]
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
    · apply IsUnit.of_mul_eq_one (3354 : ZMod 6709)
      decide
    · apply IsUnit.of_mul_eq_one (4059 : ZMod 6709)
      decide
    · apply IsUnit.of_mul_eq_one (2379 : ZMod 6709)
      decide
    · apply IsUnit.of_mul_eq_one (380 : ZMod 6709)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6719 : Nat.Prime 6719 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6719 6718 1 11 [2, 3359]
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
    · apply IsUnit.of_mul_eq_one (3359 : ZMod 6719)
      decide
    · apply IsUnit.of_mul_eq_one (56 : ZMod 6719)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6733 : Nat.Prime 6733 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6733 6732 1 2 [2, 2, 3, 3, 11, 17]
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
    · apply IsUnit.of_mul_eq_one (3366 : ZMod 6733)
      decide
    · apply IsUnit.of_mul_eq_one (206 : ZMod 6733)
      decide
    · apply IsUnit.of_mul_eq_one (1997 : ZMod 6733)
      decide
    · apply IsUnit.of_mul_eq_one (4469 : ZMod 6733)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6737 : Nat.Prime 6737 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6737 6736 1 3 [2, 2, 2, 2, 421]
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
    · apply IsUnit.of_mul_eq_one (3368 : ZMod 6737)
      decide
    · apply IsUnit.of_mul_eq_one (6471 : ZMod 6737)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6761 : Nat.Prime 6761 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6761 6760 1 3 [2, 2, 2, 5, 13, 13]
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
    · apply IsUnit.of_mul_eq_one (3380 : ZMod 6761)
      decide
    · apply IsUnit.of_mul_eq_one (2883 : ZMod 6761)
      decide
    · apply IsUnit.of_mul_eq_one (6066 : ZMod 6761)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6763 : Nat.Prime 6763 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6763 6762 1 2 [2, 3, 7, 7, 23]
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
    · apply IsUnit.of_mul_eq_one (3381 : ZMod 6763)
      decide
    · apply IsUnit.of_mul_eq_one (718 : ZMod 6763)
      decide
    · apply IsUnit.of_mul_eq_one (573 : ZMod 6763)
      decide
    · apply IsUnit.of_mul_eq_one (2861 : ZMod 6763)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6779 : Nat.Prime 6779 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6779 6778 1 2 [2, 3389]
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
    · apply IsUnit.of_mul_eq_one (3389 : ZMod 6779)
      decide
    · apply IsUnit.of_mul_eq_one (2260 : ZMod 6779)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6701) (q := 6703) (by exact lowPrime_6703) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6703) (q := 6709) (by exact lowPrime_6709) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6709) (q := 6719) (by exact lowPrime_6719) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6719) (q := 6733) (by exact lowPrime_6733) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6733) (q := 6737) (by exact lowPrime_6737) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6737) (q := 6761) (by exact lowPrime_6761) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6761) (q := 6763) (by exact lowPrime_6763) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6763) (q := 6779) (by exact lowPrime_6779) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part02_chain :
    DusartPrimeRowsChain 6701 6778 dusartPrimeRows_6637_6976_part02 := by
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
