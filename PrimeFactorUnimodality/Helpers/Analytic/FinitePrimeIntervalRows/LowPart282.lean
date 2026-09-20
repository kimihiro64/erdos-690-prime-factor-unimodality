import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 282 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_18013 : Nat.Prime 18013 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18013 18012 1 2 [2, 2, 3, 19, 79]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 18013) ^ 9006 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9006 : ZMod 18013)
      decide
    · change IsUnit ((2 : ZMod 18013) ^ 9006 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9006 : ZMod 18013)
      decide
    · change IsUnit ((2 : ZMod 18013) ^ 6004 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6780 : ZMod 18013)
      decide
    · change IsUnit ((2 : ZMod 18013) ^ 948 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8913 : ZMod 18013)
      decide
    · change IsUnit ((2 : ZMod 18013) ^ 228 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6066 : ZMod 18013)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18041 : Nat.Prime 18041 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18041 18040 1 3 [2, 2, 2, 5, 11, 41]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 18041) ^ 9020 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9020 : ZMod 18041)
      decide
    · change IsUnit ((3 : ZMod 18041) ^ 9020 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9020 : ZMod 18041)
      decide
    · change IsUnit ((3 : ZMod 18041) ^ 9020 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9020 : ZMod 18041)
      decide
    · change IsUnit ((3 : ZMod 18041) ^ 3608 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6345 : ZMod 18041)
      decide
    · change IsUnit ((3 : ZMod 18041) ^ 1640 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8339 : ZMod 18041)
      decide
    · change IsUnit ((3 : ZMod 18041) ^ 440 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8337 : ZMod 18041)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17989) (q := 18013) (by exact lowPrime_18013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 18013) (q := 18041) (by exact lowPrime_18041) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part12_chain :
    DusartPrimeRowsChain 17989 18041 dusartPrimeRows_17159_18040_part12 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.empty
      norm_num
