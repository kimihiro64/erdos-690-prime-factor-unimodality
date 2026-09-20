import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 48 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6277 : Nat.Prime 6277 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6277 6276 1 2 [2, 2, 3, 523]
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
    · apply IsUnit.of_mul_eq_one (3138 : ZMod 6277)
      decide
    · apply IsUnit.of_mul_eq_one (5507 : ZMod 6277)
      decide
    · apply IsUnit.of_mul_eq_one (210 : ZMod 6277)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6287 : Nat.Prime 6287 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6287 6286 1 7 [2, 7, 449]
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
    · apply IsUnit.of_mul_eq_one (3143 : ZMod 6287)
      decide
    · apply IsUnit.of_mul_eq_one (5345 : ZMod 6287)
      decide
    · apply IsUnit.of_mul_eq_one (4361 : ZMod 6287)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6299 : Nat.Prime 6299 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6299 6298 1 2 [2, 47, 67]
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
    · apply IsUnit.of_mul_eq_one (3149 : ZMod 6299)
      decide
    · apply IsUnit.of_mul_eq_one (5040 : ZMod 6299)
      decide
    · apply IsUnit.of_mul_eq_one (4505 : ZMod 6299)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6301 : Nat.Prime 6301 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6301 6300 1 10 [2, 2, 3, 3, 5, 5, 7]
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
    · apply IsUnit.of_mul_eq_one (3150 : ZMod 6301)
      decide
    · apply IsUnit.of_mul_eq_one (992 : ZMod 6301)
      decide
    · apply IsUnit.of_mul_eq_one (3219 : ZMod 6301)
      decide
    · apply IsUnit.of_mul_eq_one (1161 : ZMod 6301)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6311 : Nat.Prime 6311 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6311 6310 1 7 [2, 5, 631]
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
    · apply IsUnit.of_mul_eq_one (3155 : ZMod 6311)
      decide
    · apply IsUnit.of_mul_eq_one (2500 : ZMod 6311)
      decide
    · apply IsUnit.of_mul_eq_one (3495 : ZMod 6311)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6271) (q := 6277) (by exact lowPrime_6277) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6277) (q := 6287) (by exact lowPrime_6287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6287) (q := 6299) (by exact lowPrime_6299) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6299) (q := 6301) (by exact lowPrime_6301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6301) (q := 6311) (by exact lowPrime_6311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part05_chain :
    DusartPrimeRowsChain 6271 6310 dusartPrimeRows_6007_6310_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · apply DusartPrimeRowsChain.empty
            norm_num [dusartPrimeRow_of_explicit_6310, dusartPrimeRow_of_explicit_right]
