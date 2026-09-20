import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 151 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13331 : Nat.Prime 13331 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13331 13330 1 2 [2, 5, 31, 43]
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
    · apply IsUnit.of_mul_eq_one (6665 : ZMod 13331)
      decide
    · apply IsUnit.of_mul_eq_one (8391 : ZMod 13331)
      decide
    · apply IsUnit.of_mul_eq_one (4902 : ZMod 13331)
      decide
    · apply IsUnit.of_mul_eq_one (1349 : ZMod 13331)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13337 : Nat.Prime 13337 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13337 13336 1 3 [2, 2, 2, 1667]
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
    · apply IsUnit.of_mul_eq_one (6668 : ZMod 13337)
      decide
    · apply IsUnit.of_mul_eq_one (12538 : ZMod 13337)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13339 : Nat.Prime 13339 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13339 13338 1 2 [2, 3, 3, 3, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (6669 : ZMod 13339)
      decide
    · apply IsUnit.of_mul_eq_one (10196 : ZMod 13339)
      decide
    · apply IsUnit.of_mul_eq_one (5147 : ZMod 13339)
      decide
    · apply IsUnit.of_mul_eq_one (2731 : ZMod 13339)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13367 : Nat.Prime 13367 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13367 13366 1 5 [2, 41, 163]
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
    · apply IsUnit.of_mul_eq_one (6683 : ZMod 13367)
      decide
    · apply IsUnit.of_mul_eq_one (11901 : ZMod 13367)
      decide
    · apply IsUnit.of_mul_eq_one (566 : ZMod 13367)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 13327) (q := 13331) (by exact lowPrime_13331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13331) (q := 13337) (by exact lowPrime_13337) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13337) (q := 13339) (by exact lowPrime_13339) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 13339) (q := 13367) (by exact lowPrime_13367) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part09_chain :
    DusartPrimeRowsChain 13327 13366 dusartPrimeRows_12713_13366_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · apply DusartPrimeRowsChain.empty
          norm_num [dusartPrimeRow_of_explicit_13359, dusartPrimeRow_of_explicit_right]
