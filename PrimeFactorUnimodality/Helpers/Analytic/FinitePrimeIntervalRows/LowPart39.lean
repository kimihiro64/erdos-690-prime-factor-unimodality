import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 39 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5701 : Nat.Prime 5701 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5701 5700 1 2 [2, 2, 3, 5, 5, 19]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2850 : ZMod 5701)
      decide
    · apply IsUnit.of_mul_eq_one (3775 : ZMod 5701)
      decide
    · apply IsUnit.of_mul_eq_one (421 : ZMod 5701)
      decide
    · apply IsUnit.of_mul_eq_one (4625 : ZMod 5701)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5711 : Nat.Prime 5711 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5711 5710 1 19 [2, 5, 571]
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
    · apply IsUnit.of_mul_eq_one (2855 : ZMod 5711)
      decide
    · apply IsUnit.of_mul_eq_one (992 : ZMod 5711)
      decide
    · apply IsUnit.of_mul_eq_one (3596 : ZMod 5711)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5693) (q := 5701) (by exact lowPrime_5701) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5701) (q := 5711) (by exact lowPrime_5711) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part05_chain :
    DusartPrimeRowsChain 5693 5710 dusartPrimeRows_5437_5710_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · apply DusartPrimeRowsChain.empty
      norm_num [dusartPrimeRow_of_explicit_5710, dusartPrimeRow_of_explicit_right]
