import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 25 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4817 : Nat.Prime 4817 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4817 4816 1 3 [2, 2, 2, 2, 7, 43]
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
    · apply IsUnit.of_mul_eq_one (2408 : ZMod 4817)
      decide
    · apply IsUnit.of_mul_eq_one (2310 : ZMod 4817)
      decide
    · apply IsUnit.of_mul_eq_one (4804 : ZMod 4817)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4831 : Nat.Prime 4831 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4831 4830 1 3 [2, 3, 5, 7, 23]
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
    · apply IsUnit.of_mul_eq_one (2415 : ZMod 4831)
      decide
    · apply IsUnit.of_mul_eq_one (1633 : ZMod 4831)
      decide
    · apply IsUnit.of_mul_eq_one (3287 : ZMod 4831)
      decide
    · apply IsUnit.of_mul_eq_one (1231 : ZMod 4831)
      decide
    · apply IsUnit.of_mul_eq_one (1412 : ZMod 4831)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4861 : Nat.Prime 4861 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4861 4860 1 11 [2, 2, 3, 3, 3, 3, 3, 5]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2430 : ZMod 4861)
      decide
    · apply IsUnit.of_mul_eq_one (106 : ZMod 4861)
      decide
    · apply IsUnit.of_mul_eq_one (4154 : ZMod 4861)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4871 : Nat.Prime 4871 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4871 4870 1 11 [2, 5, 487]
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
    · apply IsUnit.of_mul_eq_one (2435 : ZMod 4871)
      decide
    · apply IsUnit.of_mul_eq_one (898 : ZMod 4871)
      decide
    · apply IsUnit.of_mul_eq_one (3989 : ZMod 4871)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4877 : Nat.Prime 4877 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4877 4876 1 2 [2, 2, 23, 53]
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
    · apply IsUnit.of_mul_eq_one (2438 : ZMod 4877)
      decide
    · apply IsUnit.of_mul_eq_one (3871 : ZMod 4877)
      decide
    · apply IsUnit.of_mul_eq_one (326 : ZMod 4877)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4889 : Nat.Prime 4889 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4889 4888 1 3 [2, 2, 2, 13, 47]
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
    · apply IsUnit.of_mul_eq_one (2444 : ZMod 4889)
      decide
    · apply IsUnit.of_mul_eq_one (3584 : ZMod 4889)
      decide
    · apply IsUnit.of_mul_eq_one (4116 : ZMod 4889)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4903 : Nat.Prime 4903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4903 4902 1 3 [2, 3, 19, 43]
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
    · apply IsUnit.of_mul_eq_one (2451 : ZMod 4903)
      decide
    · apply IsUnit.of_mul_eq_one (805 : ZMod 4903)
      decide
    · apply IsUnit.of_mul_eq_one (1009 : ZMod 4903)
      decide
    · apply IsUnit.of_mul_eq_one (788 : ZMod 4903)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4909 : Nat.Prime 4909 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4909 4908 1 6 [2, 2, 3, 409]
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
    · apply IsUnit.of_mul_eq_one (2454 : ZMod 4909)
      decide
    · apply IsUnit.of_mul_eq_one (1827 : ZMod 4909)
      decide
    · apply IsUnit.of_mul_eq_one (322 : ZMod 4909)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4673_4918_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4914 (p := 4813) (q := 4817) (by exact lowPrime_4817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4817) (q := 4831) (by exact lowPrime_4831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4831) (q := 4861) (by exact lowPrime_4861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4861) (q := 4871) (by exact lowPrime_4871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4871) (q := 4877) (by exact lowPrime_4877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4877) (q := 4889) (by exact lowPrime_4889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4889) (q := 4903) (by exact lowPrime_4903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4914 (p := 4903) (q := 4909) (by exact lowPrime_4909) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4673_4918_part03_chain :
    DusartPrimeRowsChain 4813 4908 dusartPrimeRows_4673_4918_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · norm_num [dusartPrimeRow_of_explicit_4914]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4914]
    · norm_num [dusartPrimeRow_of_explicit_4914]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4914]
      · norm_num [dusartPrimeRow_of_explicit_4914]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4914]
        · norm_num [dusartPrimeRow_of_explicit_4914]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4914]
          · norm_num [dusartPrimeRow_of_explicit_4914]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4914]
            · norm_num [dusartPrimeRow_of_explicit_4914]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4914]
              · norm_num [dusartPrimeRow_of_explicit_4914]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4914]
                · norm_num [dusartPrimeRow_of_explicit_4914]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4914, dusartPrimeRow_of_explicit_right]
