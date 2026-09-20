import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 64 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7297 : Nat.Prime 7297 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7297 7296 1 5 [2, 2, 2, 2, 2, 2, 2, 3, 19]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3648 : ZMod 7297)
      decide
    · apply IsUnit.of_mul_eq_one (6118 : ZMod 7297)
      decide
    · apply IsUnit.of_mul_eq_one (462 : ZMod 7297)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7307 : Nat.Prime 7307 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7307 7306 1 2 [2, 13, 281]
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
    · apply IsUnit.of_mul_eq_one (3653 : ZMod 7307)
      decide
    · apply IsUnit.of_mul_eq_one (1176 : ZMod 7307)
      decide
    · apply IsUnit.of_mul_eq_one (2960 : ZMod 7307)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7309 : Nat.Prime 7309 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7309 7308 1 6 [2, 2, 3, 3, 7, 29]
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
    · apply IsUnit.of_mul_eq_one (3654 : ZMod 7309)
      decide
    · apply IsUnit.of_mul_eq_one (1297 : ZMod 7309)
      decide
    · apply IsUnit.of_mul_eq_one (3846 : ZMod 7309)
      decide
    · apply IsUnit.of_mul_eq_one (5445 : ZMod 7309)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7321 : Nat.Prime 7321 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7321 7320 1 7 [2, 2, 2, 3, 5, 61]
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
    · apply IsUnit.of_mul_eq_one (3660 : ZMod 7321)
      decide
    · apply IsUnit.of_mul_eq_one (2337 : ZMod 7321)
      decide
    · apply IsUnit.of_mul_eq_one (3995 : ZMod 7321)
      decide
    · apply IsUnit.of_mul_eq_one (853 : ZMod 7321)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7331 : Nat.Prime 7331 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7331 7330 1 2 [2, 5, 733]
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
    · apply IsUnit.of_mul_eq_one (3665 : ZMod 7331)
      decide
    · apply IsUnit.of_mul_eq_one (5638 : ZMod 7331)
      decide
    · apply IsUnit.of_mul_eq_one (2458 : ZMod 7331)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7333 : Nat.Prime 7333 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7333 7332 1 6 [2, 2, 3, 13, 47]
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
    · apply IsUnit.of_mul_eq_one (3666 : ZMod 7333)
      decide
    · apply IsUnit.of_mul_eq_one (5909 : ZMod 7333)
      decide
    · apply IsUnit.of_mul_eq_one (2053 : ZMod 7333)
      decide
    · apply IsUnit.of_mul_eq_one (5179 : ZMod 7333)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7283) (q := 7297) (by exact lowPrime_7297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7297) (q := 7307) (by exact lowPrime_7307) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7307) (q := 7309) (by exact lowPrime_7309) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7309) (q := 7321) (by exact lowPrime_7321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7321) (q := 7331) (by exact lowPrime_7331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7331) (q := 7333) (by exact lowPrime_7333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part05_chain :
    DusartPrimeRowsChain 7283 7332 dusartPrimeRows_6977_7332_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · apply DusartPrimeRowsChain.empty
              norm_num [dusartPrimeRow_of_explicit_7331, dusartPrimeRow_of_explicit_right]
