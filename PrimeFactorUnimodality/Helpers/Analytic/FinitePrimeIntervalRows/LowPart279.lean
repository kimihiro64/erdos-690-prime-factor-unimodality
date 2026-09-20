import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 279 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17789 : Nat.Prime 17789 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17789 17788 1 2 [2, 2, 4447]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (8894 : ZMod 17789)
      decide
    · apply IsUnit.of_mul_eq_one (1186 : ZMod 17789)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17791 : Nat.Prime 17791 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17791 17790 1 3 [2, 3, 5, 593]
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
    · apply IsUnit.of_mul_eq_one (8895 : ZMod 17791)
      decide
    · apply IsUnit.of_mul_eq_one (4428 : ZMod 17791)
      decide
    · apply IsUnit.of_mul_eq_one (5012 : ZMod 17791)
      decide
    · apply IsUnit.of_mul_eq_one (3884 : ZMod 17791)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17807 : Nat.Prime 17807 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17807 17806 1 5 [2, 29, 307]
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
    · apply IsUnit.of_mul_eq_one (8903 : ZMod 17807)
      decide
    · apply IsUnit.of_mul_eq_one (11073 : ZMod 17807)
      decide
    · apply IsUnit.of_mul_eq_one (12899 : ZMod 17807)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17827 : Nat.Prime 17827 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17827 17826 1 2 [2, 3, 2971]
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
    · apply IsUnit.of_mul_eq_one (8913 : ZMod 17827)
      decide
    · apply IsUnit.of_mul_eq_one (5314 : ZMod 17827)
      decide
    · apply IsUnit.of_mul_eq_one (9055 : ZMod 17827)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17837 : Nat.Prime 17837 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17837 17836 1 2 [2, 2, 7, 7, 7, 13]
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
    · apply IsUnit.of_mul_eq_one (8918 : ZMod 17837)
      decide
    · apply IsUnit.of_mul_eq_one (7885 : ZMod 17837)
      decide
    · apply IsUnit.of_mul_eq_one (2230 : ZMod 17837)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17839 : Nat.Prime 17839 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17839 17838 1 6 [2, 3, 3, 991]
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
    · apply IsUnit.of_mul_eq_one (8919 : ZMod 17839)
      decide
    · apply IsUnit.of_mul_eq_one (16075 : ZMod 17839)
      decide
    · apply IsUnit.of_mul_eq_one (17129 : ZMod 17839)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17851 : Nat.Prime 17851 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17851 17850 1 2 [2, 3, 5, 5, 7, 17]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (8925 : ZMod 17851)
      decide
    · apply IsUnit.of_mul_eq_one (16730 : ZMod 17851)
      decide
    · apply IsUnit.of_mul_eq_one (2339 : ZMod 17851)
      decide
    · apply IsUnit.of_mul_eq_one (6976 : ZMod 17851)
      decide
    · apply IsUnit.of_mul_eq_one (5078 : ZMod 17851)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17863 : Nat.Prime 17863 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17863 17862 1 6 [2, 3, 13, 229]
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
    · apply IsUnit.of_mul_eq_one (8931 : ZMod 17863)
      decide
    · apply IsUnit.of_mul_eq_one (9184 : ZMod 17863)
      decide
    · apply IsUnit.of_mul_eq_one (11702 : ZMod 17863)
      decide
    · apply IsUnit.of_mul_eq_one (837 : ZMod 17863)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17783) (q := 17789) (by exact lowPrime_17789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17789) (q := 17791) (by exact lowPrime_17791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17791) (q := 17807) (by exact lowPrime_17807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17807) (q := 17827) (by exact lowPrime_17827) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17827) (q := 17837) (by exact lowPrime_17837) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17837) (q := 17839) (by exact lowPrime_17839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17839) (q := 17851) (by exact lowPrime_17851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17851) (q := 17863) (by exact lowPrime_17863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part09_chain :
    DusartPrimeRowsChain 17783 17862 dusartPrimeRows_17159_18040_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]
