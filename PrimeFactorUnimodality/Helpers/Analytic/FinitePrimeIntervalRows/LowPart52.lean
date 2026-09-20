import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 52 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6551 : Nat.Prime 6551 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6551 6550 1 17 [2, 5, 5, 131]
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
    · apply IsUnit.of_mul_eq_one (3275 : ZMod 6551)
      decide
    · apply IsUnit.of_mul_eq_one (5283 : ZMod 6551)
      decide
    · apply IsUnit.of_mul_eq_one (3333 : ZMod 6551)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6553 : Nat.Prime 6553 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6553 6552 1 10 [2, 2, 2, 3, 3, 7, 13]
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
    · apply IsUnit.of_mul_eq_one (3276 : ZMod 6553)
      decide
    · apply IsUnit.of_mul_eq_one (3720 : ZMod 6553)
      decide
    · apply IsUnit.of_mul_eq_one (1608 : ZMod 6553)
      decide
    · apply IsUnit.of_mul_eq_one (661 : ZMod 6553)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6563 : Nat.Prime 6563 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6563 6562 1 5 [2, 17, 193]
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
    · apply IsUnit.of_mul_eq_one (3281 : ZMod 6563)
      decide
    · apply IsUnit.of_mul_eq_one (3199 : ZMod 6563)
      decide
    · apply IsUnit.of_mul_eq_one (2244 : ZMod 6563)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6569 : Nat.Prime 6569 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6569 6568 1 3 [2, 2, 2, 821]
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
    · apply IsUnit.of_mul_eq_one (3284 : ZMod 6569)
      decide
    · apply IsUnit.of_mul_eq_one (5839 : ZMod 6569)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6571 : Nat.Prime 6571 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6571 6570 1 3 [2, 3, 3, 5, 73]
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
    · apply IsUnit.of_mul_eq_one (3285 : ZMod 6571)
      decide
    · apply IsUnit.of_mul_eq_one (3387 : ZMod 6571)
      decide
    · apply IsUnit.of_mul_eq_one (6443 : ZMod 6571)
      decide
    · apply IsUnit.of_mul_eq_one (6452 : ZMod 6571)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6577 : Nat.Prime 6577 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6577 6576 1 5 [2, 2, 2, 2, 3, 137]
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
    · apply IsUnit.of_mul_eq_one (3288 : ZMod 6577)
      decide
    · apply IsUnit.of_mul_eq_one (4502 : ZMod 6577)
      decide
    · apply IsUnit.of_mul_eq_one (2000 : ZMod 6577)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6581 : Nat.Prime 6581 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6581 6580 1 14 [2, 2, 5, 7, 47]
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
    · apply IsUnit.of_mul_eq_one (3290 : ZMod 6581)
      decide
    · apply IsUnit.of_mul_eq_one (5454 : ZMod 6581)
      decide
    · apply IsUnit.of_mul_eq_one (1674 : ZMod 6581)
      decide
    · apply IsUnit.of_mul_eq_one (369 : ZMod 6581)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6599 : Nat.Prime 6599 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6599 6598 1 13 [2, 3299]
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
    · apply IsUnit.of_mul_eq_one (3299 : ZMod 6599)
      decide
    · apply IsUnit.of_mul_eq_one (982 : ZMod 6599)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6311_6636_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6634 (p := 6547) (q := 6551) (by exact lowPrime_6551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6551) (q := 6553) (by exact lowPrime_6553) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6553) (q := 6563) (by exact lowPrime_6563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6563) (q := 6569) (by exact lowPrime_6569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6569) (q := 6571) (by exact lowPrime_6571) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6571) (q := 6577) (by exact lowPrime_6577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6577) (q := 6581) (by exact lowPrime_6581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6634 (p := 6581) (q := 6599) (by exact lowPrime_6599) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6311_6636_part04_chain :
    DusartPrimeRowsChain 6547 6598 dusartPrimeRows_6311_6636_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · norm_num [dusartPrimeRow_of_explicit_6634]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · norm_num [dusartPrimeRow_of_explicit_6634]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · norm_num [dusartPrimeRow_of_explicit_6634]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6634]
        · norm_num [dusartPrimeRow_of_explicit_6634]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6634]
          · norm_num [dusartPrimeRow_of_explicit_6634]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6634]
            · norm_num [dusartPrimeRow_of_explicit_6634]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6634]
              · norm_num [dusartPrimeRow_of_explicit_6634]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6634]
                · norm_num [dusartPrimeRow_of_explicit_6634]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6634, dusartPrimeRow_of_explicit_right]
