import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 85 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8669 : Nat.Prime 8669 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8669 8668 1 2 [2, 2, 11, 197]
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
    · apply IsUnit.of_mul_eq_one (4334 : ZMod 8669)
      decide
    · apply IsUnit.of_mul_eq_one (4722 : ZMod 8669)
      decide
    · apply IsUnit.of_mul_eq_one (5512 : ZMod 8669)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8677 : Nat.Prime 8677 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8677 8676 1 2 [2, 2, 3, 3, 241]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4338 : ZMod 8677)
      decide
    · apply IsUnit.of_mul_eq_one (8217 : ZMod 8677)
      decide
    · apply IsUnit.of_mul_eq_one (1404 : ZMod 8677)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8681 : Nat.Prime 8681 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8681 8680 1 15 [2, 2, 2, 5, 7, 31]
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
    · apply IsUnit.of_mul_eq_one (4340 : ZMod 8681)
      decide
    · apply IsUnit.of_mul_eq_one (3404 : ZMod 8681)
      decide
    · apply IsUnit.of_mul_eq_one (8175 : ZMod 8681)
      decide
    · apply IsUnit.of_mul_eq_one (6082 : ZMod 8681)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8689 : Nat.Prime 8689 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8689 8688 1 13 [2, 2, 2, 2, 3, 181]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4344 : ZMod 8689)
      decide
    · apply IsUnit.of_mul_eq_one (8054 : ZMod 8689)
      decide
    · apply IsUnit.of_mul_eq_one (4782 : ZMod 8689)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8693 : Nat.Prime 8693 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8693 8692 1 2 [2, 2, 41, 53]
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
    · apply IsUnit.of_mul_eq_one (4346 : ZMod 8693)
      decide
    · apply IsUnit.of_mul_eq_one (4368 : ZMod 8693)
      decide
    · apply IsUnit.of_mul_eq_one (3635 : ZMod 8693)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8699 : Nat.Prime 8699 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8699 8698 1 2 [2, 4349]
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
    · apply IsUnit.of_mul_eq_one (4349 : ZMod 8699)
      decide
    · apply IsUnit.of_mul_eq_one (2900 : ZMod 8699)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8707 : Nat.Prime 8707 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8707 8706 1 5 [2, 3, 1451]
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
    · apply IsUnit.of_mul_eq_one (4353 : ZMod 8707)
      decide
    · apply IsUnit.of_mul_eq_one (804 : ZMod 8707)
      decide
    · apply IsUnit.of_mul_eq_one (2544 : ZMod 8707)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8713 : Nat.Prime 8713 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8713 8712 1 5 [2, 2, 2, 3, 3, 11, 11]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4356 : ZMod 8713)
      decide
    · apply IsUnit.of_mul_eq_one (6654 : ZMod 8713)
      decide
    · apply IsUnit.of_mul_eq_one (7898 : ZMod 8713)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8663) (q := 8669) (by exact lowPrime_8669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8669) (q := 8677) (by exact lowPrime_8677) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8677) (q := 8681) (by exact lowPrime_8681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8681) (q := 8689) (by exact lowPrime_8689) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8689) (q := 8693) (by exact lowPrime_8693) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8693) (q := 8699) (by exact lowPrime_8699) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8699) (q := 8707) (by exact lowPrime_8707) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8707) (q := 8713) (by exact lowPrime_8713) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part03_chain :
    DusartPrimeRowsChain 8663 8712 dusartPrimeRows_8521_8962_part03 := by
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
        · apply DusartPrimeRowsChain.cons
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
