import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 246 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_18973 : Nat.Prime 18973 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18973 18972 1 2 [2, 2, 3, 3, 17, 31]
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
    · change IsUnit ((2 : ZMod 18973) ^ 9486 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9486 : ZMod 18973)
      decide
    · change IsUnit ((2 : ZMod 18973) ^ 9486 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9486 : ZMod 18973)
      decide
    · change IsUnit ((2 : ZMod 18973) ^ 6324 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13563 : ZMod 18973)
      decide
    · change IsUnit ((2 : ZMod 18973) ^ 6324 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13563 : ZMod 18973)
      decide
    · change IsUnit ((2 : ZMod 18973) ^ 1116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4625 : ZMod 18973)
      decide
    · change IsUnit ((2 : ZMod 18973) ^ 612 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3084 : ZMod 18973)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18979 : Nat.Prime 18979 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18979 18978 1 2 [2, 3, 3163]
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
    · change IsUnit ((2 : ZMod 18979) ^ 9489 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9489 : ZMod 18979)
      decide
    · change IsUnit ((2 : ZMod 18979) ^ 6326 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12452 : ZMod 18979)
      decide
    · change IsUnit ((2 : ZMod 18979) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17774 : ZMod 18979)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19001 : Nat.Prime 19001 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19001 19000 1 3 [2, 2, 2, 5, 5, 5, 19]
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
    · change IsUnit ((3 : ZMod 19001) ^ 9500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9500 : ZMod 19001)
      decide
    · change IsUnit ((3 : ZMod 19001) ^ 9500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9500 : ZMod 19001)
      decide
    · change IsUnit ((3 : ZMod 19001) ^ 9500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9500 : ZMod 19001)
      decide
    · change IsUnit ((3 : ZMod 19001) ^ 3800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5749 : ZMod 19001)
      decide
    · change IsUnit ((3 : ZMod 19001) ^ 3800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5749 : ZMod 19001)
      decide
    · change IsUnit ((3 : ZMod 19001) ^ 3800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5749 : ZMod 19001)
      decide
    · change IsUnit ((3 : ZMod 19001) ^ 1000 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16612 : ZMod 19001)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19009 : Nat.Prime 19009 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19009 19008 1 23 [2, 2, 2, 2, 2, 2, 3, 3, 3, 11]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((23 : ZMod 19009) ^ 9504 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9504 : ZMod 19009)
      decide
    · change IsUnit ((23 : ZMod 19009) ^ 9504 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9504 : ZMod 19009)
      decide
    · change IsUnit ((23 : ZMod 19009) ^ 9504 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9504 : ZMod 19009)
      decide
    · change IsUnit ((23 : ZMod 19009) ^ 9504 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9504 : ZMod 19009)
      decide
    · change IsUnit ((23 : ZMod 19009) ^ 9504 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9504 : ZMod 19009)
      decide
    · change IsUnit ((23 : ZMod 19009) ^ 9504 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9504 : ZMod 19009)
      decide
    · change IsUnit ((23 : ZMod 19009) ^ 6336 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5794 : ZMod 19009)
      decide
    · change IsUnit ((23 : ZMod 19009) ^ 6336 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5794 : ZMod 19009)
      decide
    · change IsUnit ((23 : ZMod 19009) ^ 6336 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5794 : ZMod 19009)
      decide
    · change IsUnit ((23 : ZMod 19009) ^ 1728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17520 : ZMod 19009)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19013 : Nat.Prime 19013 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19013 19012 1 2 [2, 2, 7, 7, 97]
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
    · change IsUnit ((2 : ZMod 19013) ^ 9506 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9506 : ZMod 19013)
      decide
    · change IsUnit ((2 : ZMod 19013) ^ 9506 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9506 : ZMod 19013)
      decide
    · change IsUnit ((2 : ZMod 19013) ^ 2716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1724 : ZMod 19013)
      decide
    · change IsUnit ((2 : ZMod 19013) ^ 2716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1724 : ZMod 19013)
      decide
    · change IsUnit ((2 : ZMod 19013) ^ 196 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1428 : ZMod 19013)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19031 : Nat.Prime 19031 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19031 19030 1 11 [2, 5, 11, 173]
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
    · change IsUnit ((11 : ZMod 19031) ^ 9515 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9515 : ZMod 19031)
      decide
    · change IsUnit ((11 : ZMod 19031) ^ 3806 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9800 : ZMod 19031)
      decide
    · change IsUnit ((11 : ZMod 19031) ^ 1730 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6465 : ZMod 19031)
      decide
    · change IsUnit ((11 : ZMod 19031) ^ 110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14062 : ZMod 19031)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19037 : Nat.Prime 19037 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19037 19036 1 2 [2, 2, 4759]
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
    · change IsUnit ((2 : ZMod 19037) ^ 9518 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9518 : ZMod 19037)
      decide
    · change IsUnit ((2 : ZMod 19037) ^ 9518 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9518 : ZMod 19037)
      decide
    · change IsUnit ((2 : ZMod 19037) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8884 : ZMod 19037)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19051 : Nat.Prime 19051 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19051 19050 1 2 [2, 3, 5, 5, 127]
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
    · change IsUnit ((2 : ZMod 19051) ^ 9525 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9525 : ZMod 19051)
      decide
    · change IsUnit ((2 : ZMod 19051) ^ 6350 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18052 : ZMod 19051)
      decide
    · change IsUnit ((2 : ZMod 19051) ^ 3810 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7686 : ZMod 19051)
      decide
    · change IsUnit ((2 : ZMod 19051) ^ 3810 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7686 : ZMod 19051)
      decide
    · change IsUnit ((2 : ZMod 19051) ^ 150 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5299 : ZMod 19051)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 18959) (q := 18973) (by exact lowPrime_18973) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 18973) (q := 18979) (by exact lowPrime_18979) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 18979) (q := 19001) (by exact lowPrime_19001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19001) (q := 19009) (by exact lowPrime_19009) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19009) (q := 19013) (by exact lowPrime_19013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19013) (q := 19031) (by exact lowPrime_19031) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19031) (q := 19037) (by exact lowPrime_19037) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19037) (q := 19051) (by exact lowPrime_19051) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part01_chain :
    DusartPrimeRowsChain 18959 19051 dusartPrimeRows_18959_19936_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num
