import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 89 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8933 : Nat.Prime 8933 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8933 8932 1 2 [2, 2, 7, 11, 29]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4466 : ZMod 8933)
      decide
    · apply IsUnit.of_mul_eq_one (6981 : ZMod 8933)
      decide
    · apply IsUnit.of_mul_eq_one (7685 : ZMod 8933)
      decide
    · apply IsUnit.of_mul_eq_one (5851 : ZMod 8933)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8941 : Nat.Prime 8941 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8941 8940 1 6 [2, 2, 3, 5, 149]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4470 : ZMod 8941)
      decide
    · apply IsUnit.of_mul_eq_one (2433 : ZMod 8941)
      decide
    · apply IsUnit.of_mul_eq_one (5138 : ZMod 8941)
      decide
    · apply IsUnit.of_mul_eq_one (3114 : ZMod 8941)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8951 : Nat.Prime 8951 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8951 8950 1 13 [2, 5, 5, 179]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4475 : ZMod 8951)
      decide
    · apply IsUnit.of_mul_eq_one (2628 : ZMod 8951)
      decide
    · apply IsUnit.of_mul_eq_one (5499 : ZMod 8951)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8963 : Nat.Prime 8963 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8963 8962 1 2 [2, 4481]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (4481 : ZMod 8963)
      decide
    · apply IsUnit.of_mul_eq_one (2988 : ZMod 8963)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8929) (q := 8933) (by exact lowPrime_8933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8933) (q := 8941) (by exact lowPrime_8941) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8941) (q := 8951) (by exact lowPrime_8951) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8951) (q := 8963) (by exact lowPrime_8963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part07_chain :
    DusartPrimeRowsChain 8929 8962 dusartPrimeRows_8521_8962_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.empty
          norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]
