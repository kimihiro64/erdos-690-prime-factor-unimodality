import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 170 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14767 : Nat.Prime 14767 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14767 14766 1 3 [2, 3, 23, 107]
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
    · apply IsUnit.of_mul_eq_one (7383 : ZMod 14767)
      decide
    · apply IsUnit.of_mul_eq_one (1676 : ZMod 14767)
      decide
    · apply IsUnit.of_mul_eq_one (13686 : ZMod 14767)
      decide
    · apply IsUnit.of_mul_eq_one (6270 : ZMod 14767)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14759) (q := 14767) (by exact lowPrime_14767) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part10_chain :
    DusartPrimeRowsChain 14759 14766 dusartPrimeRows_14051_14766_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.empty
    norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]
