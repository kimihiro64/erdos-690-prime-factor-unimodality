import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 76 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8111 : Nat.Prime 8111 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8111 8110 1 11 [2, 5, 811]
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
    · apply IsUnit.of_mul_eq_one (4055 : ZMod 8111)
      decide
    · apply IsUnit.of_mul_eq_one (7491 : ZMod 8111)
      decide
    · apply IsUnit.of_mul_eq_one (3137 : ZMod 8111)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7717_8110_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8103 (p := 8101) (q := 8111) (by exact lowPrime_8111) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7717_8110_part06_chain :
    DusartPrimeRowsChain 8101 8110 dusartPrimeRows_7717_8110_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · norm_num [dusartPrimeRow_of_explicit_8103]
  · apply DusartPrimeRowsChain.empty
    norm_num [dusartPrimeRow_of_explicit_8103, dusartPrimeRow_of_explicit_right]
