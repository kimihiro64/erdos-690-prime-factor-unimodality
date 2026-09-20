import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 26 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_4919 : Nat.Prime 4919 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4919 4918 1 13 [2, 2459]
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
    · change IsUnit ((13 : ZMod 4919) ^ 2459 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2459 : ZMod 4919)
      decide
    · change IsUnit ((13 : ZMod 4919) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (732 : ZMod 4919)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4909) (q := 4919) (by exact lowPrime_4919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part04_chain :
    DusartPrimeRowsChain 4909 4919 dusartPrimeRows_4673_4918_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · apply DusartPrimeRowsChain.empty
    norm_num
