import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 34 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5407 : Nat.Prime 5407 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5407 5406 1 3 [2, 3, 17, 53]
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
    · apply IsUnit.of_mul_eq_one (2703 : ZMod 5407)
      decide
    · apply IsUnit.of_mul_eq_one (347 : ZMod 5407)
      decide
    · apply IsUnit.of_mul_eq_one (4925 : ZMod 5407)
      decide
    · apply IsUnit.of_mul_eq_one (4042 : ZMod 5407)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5413 : Nat.Prime 5413 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5413 5412 1 5 [2, 2, 3, 11, 41]
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
    · apply IsUnit.of_mul_eq_one (2706 : ZMod 5413)
      decide
    · apply IsUnit.of_mul_eq_one (3200 : ZMod 5413)
      decide
    · apply IsUnit.of_mul_eq_one (5066 : ZMod 5413)
      decide
    · apply IsUnit.of_mul_eq_one (1957 : ZMod 5413)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5417 : Nat.Prime 5417 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5417 5416 1 3 [2, 2, 2, 677]
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
    · apply IsUnit.of_mul_eq_one (2708 : ZMod 5417)
      decide
    · apply IsUnit.of_mul_eq_one (1327 : ZMod 5417)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5419 : Nat.Prime 5419 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5419 5418 1 3 [2, 3, 3, 7, 43]
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
    · apply IsUnit.of_mul_eq_one (2709 : ZMod 5419)
      decide
    · apply IsUnit.of_mul_eq_one (42 : ZMod 5419)
      decide
    · apply IsUnit.of_mul_eq_one (5333 : ZMod 5419)
      decide
    · apply IsUnit.of_mul_eq_one (4270 : ZMod 5419)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5431 : Nat.Prime 5431 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5431 5430 1 3 [2, 3, 5, 181]
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
    · apply IsUnit.of_mul_eq_one (2715 : ZMod 5431)
      decide
    · apply IsUnit.of_mul_eq_one (2321 : ZMod 5431)
      decide
    · apply IsUnit.of_mul_eq_one (429 : ZMod 5431)
      decide
    · apply IsUnit.of_mul_eq_one (3566 : ZMod 5431)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5437 : Nat.Prime 5437 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5437 5436 1 5 [2, 2, 3, 3, 151]
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
    · apply IsUnit.of_mul_eq_one (2718 : ZMod 5437)
      decide
    · apply IsUnit.of_mul_eq_one (2867 : ZMod 5437)
      decide
    · apply IsUnit.of_mul_eq_one (3113 : ZMod 5437)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5399) (q := 5407) (by exact lowPrime_5407) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5407) (q := 5413) (by exact lowPrime_5413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5413) (q := 5417) (by exact lowPrime_5417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5417) (q := 5419) (by exact lowPrime_5419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5419) (q := 5431) (by exact lowPrime_5431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5431) (q := 5437) (by exact lowPrime_5437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part04_chain :
    DusartPrimeRowsChain 5399 5436 dusartPrimeRows_5167_5436_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · apply DusartPrimeRowsChain.empty
              norm_num [dusartPrimeRow_of_explicit_5431, dusartPrimeRow_of_explicit_right]
