import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 09 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_3793 : Nat.Prime 3793 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3793 3792 1 5 [2, 2, 2, 2, 3, 79]
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
    · change IsUnit ((5 : ZMod 3793) ^ 1896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1896 : ZMod 3793)
      decide
    · change IsUnit ((5 : ZMod 3793) ^ 1896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1896 : ZMod 3793)
      decide
    · change IsUnit ((5 : ZMod 3793) ^ 1896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1896 : ZMod 3793)
      decide
    · change IsUnit ((5 : ZMod 3793) ^ 1896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1896 : ZMod 3793)
      decide
    · change IsUnit ((5 : ZMod 3793) ^ 1264 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2172 : ZMod 3793)
      decide
    · change IsUnit ((5 : ZMod 3793) ^ 48 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1569 : ZMod 3793)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3797 : Nat.Prime 3797 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3797 3796 1 2 [2, 2, 13, 73]
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
    · change IsUnit ((2 : ZMod 3797) ^ 1898 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1898 : ZMod 3797)
      decide
    · change IsUnit ((2 : ZMod 3797) ^ 1898 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1898 : ZMod 3797)
      decide
    · change IsUnit ((2 : ZMod 3797) ^ 292 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2059 : ZMod 3797)
      decide
    · change IsUnit ((2 : ZMod 3797) ^ 52 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3357 : ZMod 3797)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3803 : Nat.Prime 3803 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3803 3802 1 2 [2, 1901]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · change IsUnit ((2 : ZMod 3803) ^ 1901 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1901 : ZMod 3803)
      decide
    · change IsUnit ((2 : ZMod 3803) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1268 : ZMod 3803)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3275_3802_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_3802 (p := 3779) (q := 3793) (by exact lowPrime_3793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3793) (q := 3797) (by exact lowPrime_3797) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_3802 (p := 3797) (q := 3803) (by exact lowPrime_3803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3275_3802_part09_chain :
    DusartPrimeRowsChain 3779 3803 dusartPrimeRows_3275_3802_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · norm_num [dusartPrimeRow_of_explicit_3802]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · norm_num [dusartPrimeRow_of_explicit_3802]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · norm_num [dusartPrimeRow_of_explicit_3802]
      · apply DusartPrimeRowsChain.empty
        norm_num
