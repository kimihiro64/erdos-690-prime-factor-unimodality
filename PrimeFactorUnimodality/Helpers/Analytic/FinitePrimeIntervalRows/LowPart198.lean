import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 198 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16729 : Nat.Prime 16729 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16729 16728 1 13 [2, 2, 2, 3, 17, 41]
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
    · apply IsUnit.of_mul_eq_one (8364 : ZMod 16729)
      decide
    · apply IsUnit.of_mul_eq_one (325 : ZMod 16729)
      decide
    · apply IsUnit.of_mul_eq_one (14273 : ZMod 16729)
      decide
    · apply IsUnit.of_mul_eq_one (1340 : ZMod 16729)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16741 : Nat.Prime 16741 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16741 16740 1 6 [2, 2, 3, 3, 3, 5, 31]
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
    · apply IsUnit.of_mul_eq_one (8370 : ZMod 16741)
      decide
    · apply IsUnit.of_mul_eq_one (3520 : ZMod 16741)
      decide
    · apply IsUnit.of_mul_eq_one (13235 : ZMod 16741)
      decide
    · apply IsUnit.of_mul_eq_one (3682 : ZMod 16741)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16747 : Nat.Prime 16747 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16747 16746 1 2 [2, 3, 2791]
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
    · apply IsUnit.of_mul_eq_one (8373 : ZMod 16747)
      decide
    · apply IsUnit.of_mul_eq_one (6345 : ZMod 16747)
      decide
    · apply IsUnit.of_mul_eq_one (6114 : ZMod 16747)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16759 : Nat.Prime 16759 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16759 16758 1 3 [2, 3, 3, 7, 7, 19]
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
    · apply IsUnit.of_mul_eq_one (8379 : ZMod 16759)
      decide
    · apply IsUnit.of_mul_eq_one (7486 : ZMod 16759)
      decide
    · apply IsUnit.of_mul_eq_one (10073 : ZMod 16759)
      decide
    · apply IsUnit.of_mul_eq_one (4462 : ZMod 16759)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16763 : Nat.Prime 16763 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16763 16762 1 2 [2, 17, 17, 29]
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
    · apply IsUnit.of_mul_eq_one (8381 : ZMod 16763)
      decide
    · apply IsUnit.of_mul_eq_one (13910 : ZMod 16763)
      decide
    · apply IsUnit.of_mul_eq_one (11981 : ZMod 16763)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16787 : Nat.Prime 16787 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16787 16786 1 2 [2, 7, 11, 109]
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
    · apply IsUnit.of_mul_eq_one (8393 : ZMod 16787)
      decide
    · apply IsUnit.of_mul_eq_one (5058 : ZMod 16787)
      decide
    · apply IsUnit.of_mul_eq_one (9470 : ZMod 16787)
      decide
    · apply IsUnit.of_mul_eq_one (14089 : ZMod 16787)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16811 : Nat.Prime 16811 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16811 16810 1 7 [2, 5, 41, 41]
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
    · apply IsUnit.of_mul_eq_one (8405 : ZMod 16811)
      decide
    · apply IsUnit.of_mul_eq_one (797 : ZMod 16811)
      decide
    · apply IsUnit.of_mul_eq_one (3638 : ZMod 16811)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16823 : Nat.Prime 16823 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16823 16822 1 5 [2, 13, 647]
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
    · apply IsUnit.of_mul_eq_one (8411 : ZMod 16823)
      decide
    · apply IsUnit.of_mul_eq_one (8826 : ZMod 16823)
      decide
    · apply IsUnit.of_mul_eq_one (14076 : ZMod 16823)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16703) (q := 16729) (by exact lowPrime_16729) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16729) (q := 16741) (by exact lowPrime_16741) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16741) (q := 16747) (by exact lowPrime_16747) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16747) (q := 16759) (by exact lowPrime_16759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16759) (q := 16763) (by exact lowPrime_16763) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16763) (q := 16787) (by exact lowPrime_16787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16787) (q := 16811) (by exact lowPrime_16811) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16811) (q := 16823) (by exact lowPrime_16823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part06_chain :
    DusartPrimeRowsChain 16703 16822 dusartPrimeRows_16319_17158_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_17154, dusartPrimeRow_of_explicit_right]
