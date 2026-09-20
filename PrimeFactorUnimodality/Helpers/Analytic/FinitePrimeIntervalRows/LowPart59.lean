import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 59 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_6977 : Nat.Prime 6977 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6977 6976 1 3 [2, 2, 2, 2, 2, 2, 109]
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
    · change IsUnit ((3 : ZMod 6977) ^ 3488 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3488 : ZMod 6977)
      decide
    · change IsUnit ((3 : ZMod 6977) ^ 3488 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3488 : ZMod 6977)
      decide
    · change IsUnit ((3 : ZMod 6977) ^ 3488 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3488 : ZMod 6977)
      decide
    · change IsUnit ((3 : ZMod 6977) ^ 3488 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3488 : ZMod 6977)
      decide
    · change IsUnit ((3 : ZMod 6977) ^ 3488 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3488 : ZMod 6977)
      decide
    · change IsUnit ((3 : ZMod 6977) ^ 3488 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3488 : ZMod 6977)
      decide
    · change IsUnit ((3 : ZMod 6977) ^ 64 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3841 : ZMod 6977)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6971) (q := 6977) (by exact lowPrime_6977) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part06_chain :
    DusartPrimeRowsChain 6971 6977 dusartPrimeRows_6637_6976_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · apply DusartPrimeRowsChain.empty
    norm_num
