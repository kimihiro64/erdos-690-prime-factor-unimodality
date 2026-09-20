import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 181 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (7755 : ZMod 15511)
      decide
    · apply IsUnit.of_mul_eq_one (12027 : ZMod 15511)
      decide
    · apply IsUnit.of_mul_eq_one (15035 : ZMod 15511)
      decide
    · apply IsUnit.of_mul_eq_one (12747 : ZMod 15511)
      decide
    · apply IsUnit.of_mul_eq_one (5002 : ZMod 15511)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
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
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (7763 : ZMod 15527)
      decide
    · apply IsUnit.of_mul_eq_one (3347 : ZMod 15527)
      decide
    · apply IsUnit.of_mul_eq_one (2631 : ZMod 15527)
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
    DusartPrimeRowsChain 15497 15526 dusartPrimeRows_14767_15526_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.empty
      norm_num [dusartPrimeRow_of_explicit_15521, dusartPrimeRow_of_explicit_right]
