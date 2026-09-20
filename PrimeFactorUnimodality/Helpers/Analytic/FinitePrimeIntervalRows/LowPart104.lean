import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 104 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_9907 : Nat.Prime 9907 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9907 9906 1 2 [2, 3, 13, 127]
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
    · change IsUnit ((2 : ZMod 9907) ^ 4953 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4953 : ZMod 9907)
      decide
    · change IsUnit ((2 : ZMod 9907) ^ 3302 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2190 : ZMod 9907)
      decide
    · change IsUnit ((2 : ZMod 9907) ^ 762 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6085 : ZMod 9907)
      decide
    · change IsUnit ((2 : ZMod 9907) ^ 78 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8864 : ZMod 9907)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9923 : Nat.Prime 9923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9923 9922 1 2 [2, 11, 11, 41]
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
    · change IsUnit ((2 : ZMod 9923) ^ 4961 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4961 : ZMod 9923)
      decide
    · change IsUnit ((2 : ZMod 9923) ^ 902 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (236 : ZMod 9923)
      decide
    · change IsUnit ((2 : ZMod 9923) ^ 902 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (236 : ZMod 9923)
      decide
    · change IsUnit ((2 : ZMod 9923) ^ 242 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5175 : ZMod 9923)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9929 : Nat.Prime 9929 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9929 9928 1 3 [2, 2, 2, 17, 73]
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
    · change IsUnit ((3 : ZMod 9929) ^ 4964 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4964 : ZMod 9929)
      decide
    · change IsUnit ((3 : ZMod 9929) ^ 4964 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4964 : ZMod 9929)
      decide
    · change IsUnit ((3 : ZMod 9929) ^ 4964 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4964 : ZMod 9929)
      decide
    · change IsUnit ((3 : ZMod 9929) ^ 584 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5034 : ZMod 9929)
      decide
    · change IsUnit ((3 : ZMod 9929) ^ 136 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9317 : ZMod 9929)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9931 : Nat.Prime 9931 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9931 9930 1 10 [2, 3, 5, 331]
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
    · change IsUnit ((10 : ZMod 9931) ^ 4965 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4965 : ZMod 9931)
      decide
    · change IsUnit ((10 : ZMod 9931) ^ 3310 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8520 : ZMod 9931)
      decide
    · change IsUnit ((10 : ZMod 9931) ^ 1986 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4557 : ZMod 9931)
      decide
    · change IsUnit ((10 : ZMod 9931) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8867 : ZMod 9931)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9941 : Nat.Prime 9941 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9941 9940 1 2 [2, 2, 5, 7, 71]
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
    · change IsUnit ((2 : ZMod 9941) ^ 4970 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4970 : ZMod 9941)
      decide
    · change IsUnit ((2 : ZMod 9941) ^ 4970 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4970 : ZMod 9941)
      decide
    · change IsUnit ((2 : ZMod 9941) ^ 1988 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (911 : ZMod 9941)
      decide
    · change IsUnit ((2 : ZMod 9941) ^ 1420 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (778 : ZMod 9941)
      decide
    · change IsUnit ((2 : ZMod 9941) ^ 140 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4064 : ZMod 9941)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9949 : Nat.Prime 9949 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9949 9948 1 2 [2, 2, 3, 829]
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
    · change IsUnit ((2 : ZMod 9949) ^ 4974 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4974 : ZMod 9949)
      decide
    · change IsUnit ((2 : ZMod 9949) ^ 4974 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4974 : ZMod 9949)
      decide
    · change IsUnit ((2 : ZMod 9949) ^ 3316 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5421 : ZMod 9949)
      decide
    · change IsUnit ((2 : ZMod 9949) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1776 : ZMod 9949)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9967 : Nat.Prime 9967 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9967 9966 1 3 [2, 3, 11, 151]
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
    · change IsUnit ((3 : ZMod 9967) ^ 4983 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4983 : ZMod 9967)
      decide
    · change IsUnit ((3 : ZMod 9967) ^ 3322 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (152 : ZMod 9967)
      decide
    · change IsUnit ((3 : ZMod 9967) ^ 906 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9247 : ZMod 9967)
      decide
    · change IsUnit ((3 : ZMod 9967) ^ 66 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1834 : ZMod 9967)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9973 : Nat.Prime 9973 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9973 9972 1 11 [2, 2, 3, 3, 277]
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
    · change IsUnit ((11 : ZMod 9973) ^ 4986 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4986 : ZMod 9973)
      decide
    · change IsUnit ((11 : ZMod 9973) ^ 4986 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4986 : ZMod 9973)
      decide
    · change IsUnit ((11 : ZMod 9973) ^ 3324 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6125 : ZMod 9973)
      decide
    · change IsUnit ((11 : ZMod 9973) ^ 3324 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6125 : ZMod 9973)
      decide
    · change IsUnit ((11 : ZMod 9973) ^ 36 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (891 : ZMod 9973)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 9901) (q := 9907) (by exact lowPrime_9907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9907) (q := 9923) (by exact lowPrime_9923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9923) (q := 9929) (by exact lowPrime_9929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9929) (q := 9931) (by exact lowPrime_9931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9931) (q := 9941) (by exact lowPrime_9941) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9941) (q := 9949) (by exact lowPrime_9949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9949) (q := 9967) (by exact lowPrime_9967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 9967) (q := 9973) (by exact lowPrime_9973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part01_chain :
    DusartPrimeRowsChain 9901 9973 dusartPrimeRows_9901_10426_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num
