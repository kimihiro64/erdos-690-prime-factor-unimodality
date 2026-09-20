import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 196 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16567 : Nat.Prime 16567 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16567 16566 1 3 [2, 3, 11, 251]
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
    · apply IsUnit.of_mul_eq_one (8283 : ZMod 16567)
      decide
    · apply IsUnit.of_mul_eq_one (7194 : ZMod 16567)
      decide
    · apply IsUnit.of_mul_eq_one (12033 : ZMod 16567)
      decide
    · apply IsUnit.of_mul_eq_one (15681 : ZMod 16567)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16573 : Nat.Prime 16573 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16573 16572 1 2 [2, 2, 3, 1381]
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
    · apply IsUnit.of_mul_eq_one (8286 : ZMod 16573)
      decide
    · apply IsUnit.of_mul_eq_one (2450 : ZMod 16573)
      decide
    · apply IsUnit.of_mul_eq_one (1975 : ZMod 16573)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16603 : Nat.Prime 16603 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16603 16602 1 2 [2, 3, 2767]
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
    · apply IsUnit.of_mul_eq_one (8301 : ZMod 16603)
      decide
    · apply IsUnit.of_mul_eq_one (14083 : ZMod 16603)
      decide
    · apply IsUnit.of_mul_eq_one (13177 : ZMod 16603)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16607 : Nat.Prime 16607 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16607 16606 1 5 [2, 19, 19, 23]
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
    · apply IsUnit.of_mul_eq_one (8303 : ZMod 16607)
      decide
    · apply IsUnit.of_mul_eq_one (4192 : ZMod 16607)
      decide
    · apply IsUnit.of_mul_eq_one (10715 : ZMod 16607)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16619 : Nat.Prime 16619 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16619 16618 1 2 [2, 7, 1187]
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
    · apply IsUnit.of_mul_eq_one (8309 : ZMod 16619)
      decide
    · apply IsUnit.of_mul_eq_one (10300 : ZMod 16619)
      decide
    · apply IsUnit.of_mul_eq_one (2183 : ZMod 16619)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16631 : Nat.Prime 16631 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16631 16630 1 19 [2, 5, 1663]
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
    · apply IsUnit.of_mul_eq_one (8315 : ZMod 16631)
      decide
    · apply IsUnit.of_mul_eq_one (15757 : ZMod 16631)
      decide
    · apply IsUnit.of_mul_eq_one (14761 : ZMod 16631)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16633 : Nat.Prime 16633 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16633 16632 1 15 [2, 2, 2, 3, 3, 3, 7, 11]
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
    · apply IsUnit.of_mul_eq_one (8316 : ZMod 16633)
      decide
    · apply IsUnit.of_mul_eq_one (4207 : ZMod 16633)
      decide
    · apply IsUnit.of_mul_eq_one (1523 : ZMod 16633)
      decide
    · apply IsUnit.of_mul_eq_one (10764 : ZMod 16633)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16649 : Nat.Prime 16649 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16649 16648 1 3 [2, 2, 2, 2081]
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
    · apply IsUnit.of_mul_eq_one (8324 : ZMod 16649)
      decide
    · apply IsUnit.of_mul_eq_one (4647 : ZMod 16649)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16561) (q := 16567) (by exact lowPrime_16567) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16567) (q := 16573) (by exact lowPrime_16573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16573) (q := 16603) (by exact lowPrime_16603) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16603) (q := 16607) (by exact lowPrime_16607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16607) (q := 16619) (by exact lowPrime_16619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16619) (q := 16631) (by exact lowPrime_16631) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16631) (q := 16633) (by exact lowPrime_16633) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16633) (q := 16649) (by exact lowPrime_16649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part04_chain :
    DusartPrimeRowsChain 16561 16648 dusartPrimeRows_16319_17158_part04 := by
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
