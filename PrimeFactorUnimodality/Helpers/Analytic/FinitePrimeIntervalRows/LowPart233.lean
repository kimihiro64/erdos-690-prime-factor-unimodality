import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 233 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_19949 : Nat.Prime 19949 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19949 19948 1 2 [2, 2, 4987]
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
    · change IsUnit ((2 : ZMod 19949) ^ 9974 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9974 : ZMod 19949)
      decide
    · change IsUnit ((2 : ZMod 19949) ^ 9974 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9974 : ZMod 19949)
      decide
    · change IsUnit ((2 : ZMod 19949) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1330 : ZMod 19949)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19961 : Nat.Prime 19961 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19961 19960 1 6 [2, 2, 2, 5, 499]
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
    · change IsUnit ((6 : ZMod 19961) ^ 9980 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9980 : ZMod 19961)
      decide
    · change IsUnit ((6 : ZMod 19961) ^ 9980 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9980 : ZMod 19961)
      decide
    · change IsUnit ((6 : ZMod 19961) ^ 9980 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9980 : ZMod 19961)
      decide
    · change IsUnit ((6 : ZMod 19961) ^ 3992 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18593 : ZMod 19961)
      decide
    · change IsUnit ((6 : ZMod 19961) ^ 40 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12847 : ZMod 19961)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19963 : Nat.Prime 19963 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19963 19962 1 2 [2, 3, 3, 1109]
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
    · change IsUnit ((2 : ZMod 19963) ^ 9981 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9981 : ZMod 19963)
      decide
    · change IsUnit ((2 : ZMod 19963) ^ 6654 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11193 : ZMod 19963)
      decide
    · change IsUnit ((2 : ZMod 19963) ^ 6654 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11193 : ZMod 19963)
      decide
    · change IsUnit ((2 : ZMod 19963) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19575 : ZMod 19963)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19973 : Nat.Prime 19973 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19973 19972 1 2 [2, 2, 4993]
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
    · change IsUnit ((2 : ZMod 19973) ^ 9986 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9986 : ZMod 19973)
      decide
    · change IsUnit ((2 : ZMod 19973) ^ 9986 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9986 : ZMod 19973)
      decide
    · change IsUnit ((2 : ZMod 19973) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17310 : ZMod 19973)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19979 : Nat.Prime 19979 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19979 19978 1 2 [2, 7, 1427]
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
    · change IsUnit ((2 : ZMod 19979) ^ 9989 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9989 : ZMod 19979)
      decide
    · change IsUnit ((2 : ZMod 19979) ^ 2854 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7432 : ZMod 19979)
      decide
    · change IsUnit ((2 : ZMod 19979) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16351 : ZMod 19979)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19991 : Nat.Prime 19991 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19991 19990 1 11 [2, 5, 1999]
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
    · change IsUnit ((11 : ZMod 19991) ^ 9995 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9995 : ZMod 19991)
      decide
    · change IsUnit ((11 : ZMod 19991) ^ 3998 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10094 : ZMod 19991)
      decide
    · change IsUnit ((11 : ZMod 19991) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (401 : ZMod 19991)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19993 : Nat.Prime 19993 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19993 19992 1 10 [2, 2, 2, 3, 7, 7, 17]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((10 : ZMod 19993) ^ 9996 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9996 : ZMod 19993)
      decide
    · change IsUnit ((10 : ZMod 19993) ^ 9996 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9996 : ZMod 19993)
      decide
    · change IsUnit ((10 : ZMod 19993) ^ 9996 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9996 : ZMod 19993)
      decide
    · change IsUnit ((10 : ZMod 19993) ^ 6664 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15315 : ZMod 19993)
      decide
    · change IsUnit ((10 : ZMod 19993) ^ 2856 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3406 : ZMod 19993)
      decide
    · change IsUnit ((10 : ZMod 19993) ^ 2856 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3406 : ZMod 19993)
      decide
    · change IsUnit ((10 : ZMod 19993) ^ 1176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3057 : ZMod 19993)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19997 : Nat.Prime 19997 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19997 19996 1 2 [2, 2, 4999]
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
    · change IsUnit ((2 : ZMod 19997) ^ 9998 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9998 : ZMod 19997)
      decide
    · change IsUnit ((2 : ZMod 19997) ^ 9998 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9998 : ZMod 19997)
      decide
    · change IsUnit ((2 : ZMod 19997) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9332 : ZMod 19997)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 19937) (q := 19949) (by exact lowPrime_19949) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19949) (q := 19961) (by exact lowPrime_19961) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19961) (q := 19963) (by exact lowPrime_19963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19963) (q := 19973) (by exact lowPrime_19973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19973) (q := 19979) (by exact lowPrime_19979) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19979) (q := 19991) (by exact lowPrime_19991) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19991) (q := 19993) (by exact lowPrime_19993) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 19993) (q := 19997) (by exact lowPrime_19997) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part01_chain :
    DusartPrimeRowsChain 19937 19997 dusartPrimeRows_19937_20958_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · apply DusartPrimeRowsChain.empty
                  norm_num
