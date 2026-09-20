import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 181 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_15511 : Nat.Prime 15511 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15511 15510 1 3 [2, 3, 5, 11, 47]
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
    · change IsUnit ((3 : ZMod 15511) ^ 7755 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7755 : ZMod 15511)
      decide
    · change IsUnit ((3 : ZMod 15511) ^ 5170 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12027 : ZMod 15511)
      decide
    · change IsUnit ((3 : ZMod 15511) ^ 3102 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15035 : ZMod 15511)
      decide
    · change IsUnit ((3 : ZMod 15511) ^ 1410 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12747 : ZMod 15511)
      decide
    · change IsUnit ((3 : ZMod 15511) ^ 330 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5002 : ZMod 15511)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15527 : Nat.Prime 15527 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15527 15526 1 5 [2, 7, 1109]
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
    · change IsUnit ((5 : ZMod 15527) ^ 7763 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7763 : ZMod 15527)
      decide
    · change IsUnit ((5 : ZMod 15527) ^ 2218 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3347 : ZMod 15527)
      decide
    · change IsUnit ((5 : ZMod 15527) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2631 : ZMod 15527)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15497) (q := 15511) (by exact lowPrime_15511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15511) (q := 15527) (by exact lowPrime_15527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part11_chain :
    DusartPrimeRowsChain 15497 15527 dusartPrimeRows_14767_15526_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.empty
      norm_num
