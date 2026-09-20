import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 88 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_8849 : Nat.Prime 8849 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8849 8848 1 3 [2, 2, 2, 2, 7, 79]
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
    · change IsUnit ((3 : ZMod 8849) ^ 4424 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4424 : ZMod 8849)
      decide
    · change IsUnit ((3 : ZMod 8849) ^ 4424 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4424 : ZMod 8849)
      decide
    · change IsUnit ((3 : ZMod 8849) ^ 4424 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4424 : ZMod 8849)
      decide
    · change IsUnit ((3 : ZMod 8849) ^ 4424 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4424 : ZMod 8849)
      decide
    · change IsUnit ((3 : ZMod 8849) ^ 1264 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8684 : ZMod 8849)
      decide
    · change IsUnit ((3 : ZMod 8849) ^ 112 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6705 : ZMod 8849)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8861 : Nat.Prime 8861 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8861 8860 1 2 [2, 2, 5, 443]
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
    · change IsUnit ((2 : ZMod 8861) ^ 4430 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4430 : ZMod 8861)
      decide
    · change IsUnit ((2 : ZMod 8861) ^ 4430 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4430 : ZMod 8861)
      decide
    · change IsUnit ((2 : ZMod 8861) ^ 1772 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2126 : ZMod 8861)
      decide
    · change IsUnit ((2 : ZMod 8861) ^ 20 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2152 : ZMod 8861)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8863 : Nat.Prime 8863 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8863 8862 1 3 [2, 3, 7, 211]
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
    · change IsUnit ((3 : ZMod 8863) ^ 4431 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4431 : ZMod 8863)
      decide
    · change IsUnit ((3 : ZMod 8863) ^ 2954 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3441 : ZMod 8863)
      decide
    · change IsUnit ((3 : ZMod 8863) ^ 1266 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7602 : ZMod 8863)
      decide
    · change IsUnit ((3 : ZMod 8863) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2442 : ZMod 8863)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8867 : Nat.Prime 8867 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8867 8866 1 2 [2, 11, 13, 31]
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
    · change IsUnit ((2 : ZMod 8867) ^ 4433 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4433 : ZMod 8867)
      decide
    · change IsUnit ((2 : ZMod 8867) ^ 806 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3248 : ZMod 8867)
      decide
    · change IsUnit ((2 : ZMod 8867) ^ 682 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7391 : ZMod 8867)
      decide
    · change IsUnit ((2 : ZMod 8867) ^ 286 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3741 : ZMod 8867)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8887 : Nat.Prime 8887 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8887 8886 1 3 [2, 3, 1481]
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
    · change IsUnit ((3 : ZMod 8887) ^ 4443 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4443 : ZMod 8887)
      decide
    · change IsUnit ((3 : ZMod 8887) ^ 2962 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4515 : ZMod 8887)
      decide
    · change IsUnit ((3 : ZMod 8887) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7239 : ZMod 8887)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8893 : Nat.Prime 8893 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8893 8892 1 5 [2, 2, 3, 3, 13, 19]
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
    · change IsUnit ((5 : ZMod 8893) ^ 4446 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4446 : ZMod 8893)
      decide
    · change IsUnit ((5 : ZMod 8893) ^ 4446 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4446 : ZMod 8893)
      decide
    · change IsUnit ((5 : ZMod 8893) ^ 2964 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5845 : ZMod 8893)
      decide
    · change IsUnit ((5 : ZMod 8893) ^ 2964 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5845 : ZMod 8893)
      decide
    · change IsUnit ((5 : ZMod 8893) ^ 684 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5146 : ZMod 8893)
      decide
    · change IsUnit ((5 : ZMod 8893) ^ 468 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5017 : ZMod 8893)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8923 : Nat.Prime 8923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8923 8922 1 2 [2, 3, 1487]
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
    · change IsUnit ((2 : ZMod 8923) ^ 4461 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4461 : ZMod 8923)
      decide
    · change IsUnit ((2 : ZMod 8923) ^ 2974 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1282 : ZMod 8923)
      decide
    · change IsUnit ((2 : ZMod 8923) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1558 : ZMod 8923)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8929 : Nat.Prime 8929 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8929 8928 1 11 [2, 2, 2, 2, 2, 3, 3, 31]
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
    · change IsUnit ((11 : ZMod 8929) ^ 4464 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4464 : ZMod 8929)
      decide
    · change IsUnit ((11 : ZMod 8929) ^ 4464 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4464 : ZMod 8929)
      decide
    · change IsUnit ((11 : ZMod 8929) ^ 4464 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4464 : ZMod 8929)
      decide
    · change IsUnit ((11 : ZMod 8929) ^ 4464 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4464 : ZMod 8929)
      decide
    · change IsUnit ((11 : ZMod 8929) ^ 4464 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4464 : ZMod 8929)
      decide
    · change IsUnit ((11 : ZMod 8929) ^ 2976 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7482 : ZMod 8929)
      decide
    · change IsUnit ((11 : ZMod 8929) ^ 2976 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7482 : ZMod 8929)
      decide
    · change IsUnit ((11 : ZMod 8929) ^ 288 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (732 : ZMod 8929)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8839) (q := 8849) (by exact lowPrime_8849) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8849) (q := 8861) (by exact lowPrime_8861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8861) (q := 8863) (by exact lowPrime_8863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8863) (q := 8867) (by exact lowPrime_8867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8867) (q := 8887) (by exact lowPrime_8887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8887) (q := 8893) (by exact lowPrime_8893) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8893) (q := 8923) (by exact lowPrime_8923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8923) (q := 8929) (by exact lowPrime_8929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part06_chain :
    DusartPrimeRowsChain 8839 8929 dusartPrimeRows_8521_8962_part06 := by
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
                  norm_num
