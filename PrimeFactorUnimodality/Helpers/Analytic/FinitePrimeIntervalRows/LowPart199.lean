import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 199 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16829 : Nat.Prime 16829 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16829 16828 1 2 [2, 2, 7, 601]
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
    · apply IsUnit.of_mul_eq_one (8414 : ZMod 16829)
      decide
    · apply IsUnit.of_mul_eq_one (5286 : ZMod 16829)
      decide
    · apply IsUnit.of_mul_eq_one (8719 : ZMod 16829)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16831 : Nat.Prime 16831 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16831 16830 1 6 [2, 3, 3, 5, 11, 17]
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
    · apply IsUnit.of_mul_eq_one (8415 : ZMod 16831)
      decide
    · apply IsUnit.of_mul_eq_one (6238 : ZMod 16831)
      decide
    · apply IsUnit.of_mul_eq_one (14600 : ZMod 16831)
      decide
    · apply IsUnit.of_mul_eq_one (8242 : ZMod 16831)
      decide
    · apply IsUnit.of_mul_eq_one (12925 : ZMod 16831)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16843 : Nat.Prime 16843 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16843 16842 1 2 [2, 3, 7, 401]
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
    · apply IsUnit.of_mul_eq_one (8421 : ZMod 16843)
      decide
    · apply IsUnit.of_mul_eq_one (3473 : ZMod 16843)
      decide
    · apply IsUnit.of_mul_eq_one (9970 : ZMod 16843)
      decide
    · apply IsUnit.of_mul_eq_one (13658 : ZMod 16843)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16871 : Nat.Prime 16871 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16871 16870 1 17 [2, 5, 7, 241]
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
    · apply IsUnit.of_mul_eq_one (8435 : ZMod 16871)
      decide
    · apply IsUnit.of_mul_eq_one (12599 : ZMod 16871)
      decide
    · apply IsUnit.of_mul_eq_one (3606 : ZMod 16871)
      decide
    · apply IsUnit.of_mul_eq_one (15674 : ZMod 16871)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16879 : Nat.Prime 16879 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16879 16878 1 3 [2, 3, 29, 97]
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
    · apply IsUnit.of_mul_eq_one (8439 : ZMod 16879)
      decide
    · apply IsUnit.of_mul_eq_one (12640 : ZMod 16879)
      decide
    · apply IsUnit.of_mul_eq_one (3130 : ZMod 16879)
      decide
    · apply IsUnit.of_mul_eq_one (954 : ZMod 16879)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16883 : Nat.Prime 16883 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16883 16882 1 2 [2, 23, 367]
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
    · apply IsUnit.of_mul_eq_one (8441 : ZMod 16883)
      decide
    · apply IsUnit.of_mul_eq_one (212 : ZMod 16883)
      decide
    · apply IsUnit.of_mul_eq_one (10012 : ZMod 16883)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16889 : Nat.Prime 16889 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16889 16888 1 3 [2, 2, 2, 2111]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (8444 : ZMod 16889)
      decide
    · apply IsUnit.of_mul_eq_one (10275 : ZMod 16889)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16901 : Nat.Prime 16901 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16901 16900 1 2 [2, 2, 5, 5, 13, 13]
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
    · apply IsUnit.of_mul_eq_one (8450 : ZMod 16901)
      decide
    · apply IsUnit.of_mul_eq_one (9164 : ZMod 16901)
      decide
    · apply IsUnit.of_mul_eq_one (4377 : ZMod 16901)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16823) (q := 16829) (by exact lowPrime_16829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16829) (q := 16831) (by exact lowPrime_16831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16831) (q := 16843) (by exact lowPrime_16843) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16843) (q := 16871) (by exact lowPrime_16871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16871) (q := 16879) (by exact lowPrime_16879) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16879) (q := 16883) (by exact lowPrime_16883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16883) (q := 16889) (by exact lowPrime_16889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16889) (q := 16901) (by exact lowPrime_16901) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part07_chain :
    DusartPrimeRowsChain 16823 16900 dusartPrimeRows_16319_17158_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_17154, dusartPrimeRow_of_explicit_right]
