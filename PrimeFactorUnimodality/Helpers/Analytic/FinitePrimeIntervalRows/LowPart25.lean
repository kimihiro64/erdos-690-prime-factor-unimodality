import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 25 -/

namespace PrimeFactorUnimodality

noncomputable section
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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 4817) ^ 2408 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2408 : ZMod 4817)
      decide
    · change IsUnit ((3 : ZMod 4817) ^ 2408 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2408 : ZMod 4817)
      decide
    · change IsUnit ((3 : ZMod 4817) ^ 2408 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2408 : ZMod 4817)
      decide
    · change IsUnit ((3 : ZMod 4817) ^ 2408 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2408 : ZMod 4817)
      decide
    · change IsUnit ((3 : ZMod 4817) ^ 688 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2310 : ZMod 4817)
      decide
    · change IsUnit ((3 : ZMod 4817) ^ 112 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4804 : ZMod 4817)
      decide
  · norm_num

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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 4831) ^ 2415 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2415 : ZMod 4831)
      decide
    · change IsUnit ((3 : ZMod 4831) ^ 1610 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1633 : ZMod 4831)
      decide
    · change IsUnit ((3 : ZMod 4831) ^ 966 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3287 : ZMod 4831)
      decide
    · change IsUnit ((3 : ZMod 4831) ^ 690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1231 : ZMod 4831)
      decide
    · change IsUnit ((3 : ZMod 4831) ^ 210 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1412 : ZMod 4831)
      decide
  · norm_num

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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((11 : ZMod 4861) ^ 2430 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2430 : ZMod 4861)
      decide
    · change IsUnit ((11 : ZMod 4861) ^ 2430 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2430 : ZMod 4861)
      decide
    · change IsUnit ((11 : ZMod 4861) ^ 1620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (106 : ZMod 4861)
      decide
    · change IsUnit ((11 : ZMod 4861) ^ 1620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (106 : ZMod 4861)
      decide
    · change IsUnit ((11 : ZMod 4861) ^ 1620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (106 : ZMod 4861)
      decide
    · change IsUnit ((11 : ZMod 4861) ^ 1620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (106 : ZMod 4861)
      decide
    · change IsUnit ((11 : ZMod 4861) ^ 1620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (106 : ZMod 4861)
      decide
    · change IsUnit ((11 : ZMod 4861) ^ 972 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4154 : ZMod 4861)
      decide
  · norm_num

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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((11 : ZMod 4871) ^ 2435 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2435 : ZMod 4871)
      decide
    · change IsUnit ((11 : ZMod 4871) ^ 974 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (898 : ZMod 4871)
      decide
    · change IsUnit ((11 : ZMod 4871) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3989 : ZMod 4871)
      decide
  · norm_num

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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 4877) ^ 2438 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2438 : ZMod 4877)
      decide
    · change IsUnit ((2 : ZMod 4877) ^ 2438 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2438 : ZMod 4877)
      decide
    · change IsUnit ((2 : ZMod 4877) ^ 212 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3871 : ZMod 4877)
      decide
    · change IsUnit ((2 : ZMod 4877) ^ 92 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (326 : ZMod 4877)
      decide
  · norm_num

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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 4889) ^ 2444 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2444 : ZMod 4889)
      decide
    · change IsUnit ((3 : ZMod 4889) ^ 2444 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2444 : ZMod 4889)
      decide
    · change IsUnit ((3 : ZMod 4889) ^ 2444 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2444 : ZMod 4889)
      decide
    · change IsUnit ((3 : ZMod 4889) ^ 376 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3584 : ZMod 4889)
      decide
    · change IsUnit ((3 : ZMod 4889) ^ 104 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4116 : ZMod 4889)
      decide
  · norm_num

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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 4903) ^ 2451 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2451 : ZMod 4903)
      decide
    · change IsUnit ((3 : ZMod 4903) ^ 1634 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (805 : ZMod 4903)
      decide
    · change IsUnit ((3 : ZMod 4903) ^ 258 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1009 : ZMod 4903)
      decide
    · change IsUnit ((3 : ZMod 4903) ^ 114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (788 : ZMod 4903)
      decide
  · norm_num

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
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((6 : ZMod 4909) ^ 2454 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2454 : ZMod 4909)
      decide
    · change IsUnit ((6 : ZMod 4909) ^ 2454 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2454 : ZMod 4909)
      decide
    · change IsUnit ((6 : ZMod 4909) ^ 1636 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1827 : ZMod 4909)
      decide
    · change IsUnit ((6 : ZMod 4909) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (322 : ZMod 4909)
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
    DusartPrimeRowsChain 4813 4909 dusartPrimeRows_4673_4918_part03 := by
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
                  norm_num
