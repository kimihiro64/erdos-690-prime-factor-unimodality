import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 192 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16319 : Nat.Prime 16319 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16319 16318 1 7 [2, 41, 199]
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
    · apply IsUnit.of_mul_eq_one (8159 : ZMod 16319)
      decide
    · apply IsUnit.of_mul_eq_one (5651 : ZMod 16319)
      decide
    · apply IsUnit.of_mul_eq_one (10146 : ZMod 16319)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 16301) (q := 16319) (by exact lowPrime_16319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part11_chain :
    DusartPrimeRowsChain 16301 16318 dusartPrimeRows_15527_16318_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · apply DusartPrimeRowsChain.empty
    norm_num [dusartPrimeRow_of_explicit_16317, dusartPrimeRow_of_explicit_right]
