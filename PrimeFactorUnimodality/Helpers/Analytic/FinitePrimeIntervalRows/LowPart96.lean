import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 96 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_9403 : Nat.Prime 9403 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9403 9402 1 3 [2, 3, 1567]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 9403) ^ 4701 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4701 : ZMod 9403)
      decide
    · change IsUnit ((3 : ZMod 9403) ^ 3134 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1997 : ZMod 9403)
      decide
    · change IsUnit ((3 : ZMod 9403) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7091 : ZMod 9403)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9413 : Nat.Prime 9413 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9413 9412 1 3 [2, 2, 13, 181]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 9413) ^ 4706 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4706 : ZMod 9413)
      decide
    · change IsUnit ((3 : ZMod 9413) ^ 4706 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4706 : ZMod 9413)
      decide
    · change IsUnit ((3 : ZMod 9413) ^ 724 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6022 : ZMod 9413)
      decide
    · change IsUnit ((3 : ZMod 9413) ^ 52 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8893 : ZMod 9413)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9419 : Nat.Prime 9419 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9419 9418 1 2 [2, 17, 277]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 9419) ^ 4709 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4709 : ZMod 9419)
      decide
    · change IsUnit ((2 : ZMod 9419) ^ 554 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7868 : ZMod 9419)
      decide
    · change IsUnit ((2 : ZMod 9419) ^ 34 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2495 : ZMod 9419)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9397) (q := 9403) (by exact lowPrime_9403) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9403) (q := 9413) (by exact lowPrime_9413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9413) (q := 9419) (by exact lowPrime_9419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part07_chain :
    DusartPrimeRowsChain 9397 9419 dusartPrimeRows_8963_9418_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · apply DusartPrimeRowsChain.empty
        norm_num
