import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 258 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_19927 : Nat.Prime 19927 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19927 19926 1 6 [2, 3, 3, 3, 3, 3, 41]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((6 : ZMod 19927) ^ 9963 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9963 : ZMod 19927)
      decide
    · change IsUnit ((6 : ZMod 19927) ^ 6642 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (81 : ZMod 19927)
      decide
    · change IsUnit ((6 : ZMod 19927) ^ 6642 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (81 : ZMod 19927)
      decide
    · change IsUnit ((6 : ZMod 19927) ^ 6642 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (81 : ZMod 19927)
      decide
    · change IsUnit ((6 : ZMod 19927) ^ 6642 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (81 : ZMod 19927)
      decide
    · change IsUnit ((6 : ZMod 19927) ^ 6642 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (81 : ZMod 19927)
      decide
    · change IsUnit ((6 : ZMod 19927) ^ 486 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3982 : ZMod 19927)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19937 : Nat.Prime 19937 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19937 19936 1 3 [2, 2, 2, 2, 2, 7, 89]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 19937) ^ 9968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9968 : ZMod 19937)
      decide
    · change IsUnit ((3 : ZMod 19937) ^ 9968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9968 : ZMod 19937)
      decide
    · change IsUnit ((3 : ZMod 19937) ^ 9968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9968 : ZMod 19937)
      decide
    · change IsUnit ((3 : ZMod 19937) ^ 9968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9968 : ZMod 19937)
      decide
    · change IsUnit ((3 : ZMod 19937) ^ 9968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9968 : ZMod 19937)
      decide
    · change IsUnit ((3 : ZMod 19937) ^ 2848 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11232 : ZMod 19937)
      decide
    · change IsUnit ((3 : ZMod 19937) ^ 224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12798 : ZMod 19937)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19919) (q := 19927) (by exact lowPrime_19927) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19927) (q := 19937) (by exact lowPrime_19937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part13_chain :
    DusartPrimeRowsChain 19919 19937 dusartPrimeRows_18959_19936_part13 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.empty
      norm_num
