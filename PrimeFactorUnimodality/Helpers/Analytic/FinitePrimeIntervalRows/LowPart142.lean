import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 142 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12653 : Nat.Prime 12653 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12653 12652 1 2 [2, 2, 3163]
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
    · apply IsUnit.of_mul_eq_one (6326 : ZMod 12653)
      decide
    · apply IsUnit.of_mul_eq_one (10966 : ZMod 12653)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12659 : Nat.Prime 12659 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12659 12658 1 2 [2, 6329]
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
    · apply IsUnit.of_mul_eq_one (6329 : ZMod 12659)
      decide
    · apply IsUnit.of_mul_eq_one (4220 : ZMod 12659)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12671 : Nat.Prime 12671 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12671 12670 1 14 [2, 5, 7, 181]
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
    · apply IsUnit.of_mul_eq_one (6335 : ZMod 12671)
      decide
    · apply IsUnit.of_mul_eq_one (5372 : ZMod 12671)
      decide
    · apply IsUnit.of_mul_eq_one (9543 : ZMod 12671)
      decide
    · apply IsUnit.of_mul_eq_one (4836 : ZMod 12671)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12689 : Nat.Prime 12689 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12689 12688 1 3 [2, 2, 2, 2, 13, 61]
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
    · apply IsUnit.of_mul_eq_one (6344 : ZMod 12689)
      decide
    · apply IsUnit.of_mul_eq_one (11382 : ZMod 12689)
      decide
    · apply IsUnit.of_mul_eq_one (11571 : ZMod 12689)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12697 : Nat.Prime 12697 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12697 12696 1 7 [2, 2, 2, 3, 23, 23]
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
    · apply IsUnit.of_mul_eq_one (6348 : ZMod 12697)
      decide
    · apply IsUnit.of_mul_eq_one (8031 : ZMod 12697)
      decide
    · apply IsUnit.of_mul_eq_one (3721 : ZMod 12697)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12703 : Nat.Prime 12703 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12703 12702 1 3 [2, 3, 29, 73]
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
    · apply IsUnit.of_mul_eq_one (6351 : ZMod 12703)
      decide
    · apply IsUnit.of_mul_eq_one (2449 : ZMod 12703)
      decide
    · apply IsUnit.of_mul_eq_one (9325 : ZMod 12703)
      decide
    · apply IsUnit.of_mul_eq_one (9787 : ZMod 12703)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12713 : Nat.Prime 12713 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12713 12712 1 3 [2, 2, 2, 7, 227]
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
    · apply IsUnit.of_mul_eq_one (6356 : ZMod 12713)
      decide
    · apply IsUnit.of_mul_eq_one (4119 : ZMod 12713)
      decide
    · apply IsUnit.of_mul_eq_one (11856 : ZMod 12713)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12647) (q := 12653) (by exact lowPrime_12653) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12653) (q := 12659) (by exact lowPrime_12659) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12659) (q := 12671) (by exact lowPrime_12671) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12671) (q := 12689) (by exact lowPrime_12689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12689) (q := 12697) (by exact lowPrime_12697) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12697) (q := 12703) (by exact lowPrime_12703) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12703) (q := 12713) (by exact lowPrime_12713) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part09_chain :
    DusartPrimeRowsChain 12647 12712 dusartPrimeRows_12097_12712_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.empty
                norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]
