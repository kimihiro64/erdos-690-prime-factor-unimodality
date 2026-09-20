import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 11 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_3881 : Nat.Prime 3881 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3881 3880 1 13 [2, 2, 2, 5, 97]
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
    · change IsUnit ((13 : ZMod 3881) ^ 1940 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1940 : ZMod 3881)
      decide
    · change IsUnit ((13 : ZMod 3881) ^ 1940 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1940 : ZMod 3881)
      decide
    · change IsUnit ((13 : ZMod 3881) ^ 1940 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1940 : ZMod 3881)
      decide
    · change IsUnit ((13 : ZMod 3881) ^ 776 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1358 : ZMod 3881)
      decide
    · change IsUnit ((13 : ZMod 3881) ^ 40 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2283 : ZMod 3881)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3889 : Nat.Prime 3889 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3889 3888 1 11 [2, 2, 2, 2, 3, 3, 3, 3, 3]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((11 : ZMod 3889) ^ 1944 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1944 : ZMod 3889)
      decide
    · change IsUnit ((11 : ZMod 3889) ^ 1944 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1944 : ZMod 3889)
      decide
    · change IsUnit ((11 : ZMod 3889) ^ 1944 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1944 : ZMod 3889)
      decide
    · change IsUnit ((11 : ZMod 3889) ^ 1944 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1944 : ZMod 3889)
      decide
    · change IsUnit ((11 : ZMod 3889) ^ 1296 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1962 : ZMod 3889)
      decide
    · change IsUnit ((11 : ZMod 3889) ^ 1296 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1962 : ZMod 3889)
      decide
    · change IsUnit ((11 : ZMod 3889) ^ 1296 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1962 : ZMod 3889)
      decide
    · change IsUnit ((11 : ZMod 3889) ^ 1296 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1962 : ZMod 3889)
      decide
    · change IsUnit ((11 : ZMod 3889) ^ 1296 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1962 : ZMod 3889)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3907 : Nat.Prime 3907 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3907 3906 1 2 [2, 3, 3, 7, 31]
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
    · change IsUnit ((2 : ZMod 3907) ^ 1953 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1953 : ZMod 3907)
      decide
    · change IsUnit ((2 : ZMod 3907) ^ 1302 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2625 : ZMod 3907)
      decide
    · change IsUnit ((2 : ZMod 3907) ^ 1302 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2625 : ZMod 3907)
      decide
    · change IsUnit ((2 : ZMod 3907) ^ 558 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (90 : ZMod 3907)
      decide
    · change IsUnit ((2 : ZMod 3907) ^ 126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (832 : ZMod 3907)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3911 : Nat.Prime 3911 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3911 3910 1 13 [2, 5, 17, 23]
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
    · change IsUnit ((13 : ZMod 3911) ^ 1955 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1955 : ZMod 3911)
      decide
    · change IsUnit ((13 : ZMod 3911) ^ 782 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2216 : ZMod 3911)
      decide
    · change IsUnit ((13 : ZMod 3911) ^ 230 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3501 : ZMod 3911)
      decide
    · change IsUnit ((13 : ZMod 3911) ^ 170 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1104 : ZMod 3911)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3917 : Nat.Prime 3917 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3917 3916 1 2 [2, 2, 11, 89]
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
    · change IsUnit ((2 : ZMod 3917) ^ 1958 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1958 : ZMod 3917)
      decide
    · change IsUnit ((2 : ZMod 3917) ^ 1958 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1958 : ZMod 3917)
      decide
    · change IsUnit ((2 : ZMod 3917) ^ 356 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (312 : ZMod 3917)
      decide
    · change IsUnit ((2 : ZMod 3917) ^ 44 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (853 : ZMod 3917)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3919 : Nat.Prime 3919 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3919 3918 1 3 [2, 3, 653]
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
    · change IsUnit ((3 : ZMod 3919) ^ 1959 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1959 : ZMod 3919)
      decide
    · change IsUnit ((3 : ZMod 3919) ^ 1306 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3002 : ZMod 3919)
      decide
    · change IsUnit ((3 : ZMod 3919) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3020 : ZMod 3919)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3923 : Nat.Prime 3923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3923 3922 1 2 [2, 37, 53]
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
    · change IsUnit ((2 : ZMod 3923) ^ 1961 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1961 : ZMod 3923)
      decide
    · change IsUnit ((2 : ZMod 3923) ^ 106 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2009 : ZMod 3923)
      decide
    · change IsUnit ((2 : ZMod 3923) ^ 74 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1754 : ZMod 3923)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3929 : Nat.Prime 3929 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3929 3928 1 3 [2, 2, 2, 491]
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
    · change IsUnit ((3 : ZMod 3929) ^ 1964 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1964 : ZMod 3929)
      decide
    · change IsUnit ((3 : ZMod 3929) ^ 1964 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1964 : ZMod 3929)
      decide
    · change IsUnit ((3 : ZMod 3929) ^ 1964 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1964 : ZMod 3929)
      decide
    · change IsUnit ((3 : ZMod 3929) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2582 : ZMod 3929)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3877) (q := 3881) (by exact lowPrime_3881) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3881) (q := 3889) (by exact lowPrime_3889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3889) (q := 3907) (by exact lowPrime_3907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3907) (q := 3911) (by exact lowPrime_3911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3911) (q := 3917) (by exact lowPrime_3917) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3917) (q := 3919) (by exact lowPrime_3919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3919) (q := 3923) (by exact lowPrime_3923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3923) (q := 3929) (by exact lowPrime_3929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part02_chain :
    DusartPrimeRowsChain 3877 3929 dusartPrimeRows_3803_4672_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num
