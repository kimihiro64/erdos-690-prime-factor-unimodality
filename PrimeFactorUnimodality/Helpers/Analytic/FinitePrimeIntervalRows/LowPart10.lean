import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 10 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_3821 : Nat.Prime 3821 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3821 3820 1 3 [2, 2, 5, 191]
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
    · change IsUnit ((3 : ZMod 3821) ^ 1910 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1910 : ZMod 3821)
      decide
    · change IsUnit ((3 : ZMod 3821) ^ 1910 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1910 : ZMod 3821)
      decide
    · change IsUnit ((3 : ZMod 3821) ^ 764 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1350 : ZMod 3821)
      decide
    · change IsUnit ((3 : ZMod 3821) ^ 20 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2270 : ZMod 3821)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3823 : Nat.Prime 3823 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3823 3822 1 3 [2, 3, 7, 7, 13]
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
    · change IsUnit ((3 : ZMod 3823) ^ 1911 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1911 : ZMod 3823)
      decide
    · change IsUnit ((3 : ZMod 3823) ^ 1274 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2943 : ZMod 3823)
      decide
    · change IsUnit ((3 : ZMod 3823) ^ 546 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1305 : ZMod 3823)
      decide
    · change IsUnit ((3 : ZMod 3823) ^ 546 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1305 : ZMod 3823)
      decide
    · change IsUnit ((3 : ZMod 3823) ^ 294 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1194 : ZMod 3823)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3833 : Nat.Prime 3833 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3833 3832 1 3 [2, 2, 2, 479]
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
    · change IsUnit ((3 : ZMod 3833) ^ 1916 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1916 : ZMod 3833)
      decide
    · change IsUnit ((3 : ZMod 3833) ^ 1916 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1916 : ZMod 3833)
      decide
    · change IsUnit ((3 : ZMod 3833) ^ 1916 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1916 : ZMod 3833)
      decide
    · change IsUnit ((3 : ZMod 3833) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3379 : ZMod 3833)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3847 : Nat.Prime 3847 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3847 3846 1 5 [2, 3, 641]
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
    · change IsUnit ((5 : ZMod 3847) ^ 1923 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1923 : ZMod 3847)
      decide
    · change IsUnit ((5 : ZMod 3847) ^ 1282 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3195 : ZMod 3847)
      decide
    · change IsUnit ((5 : ZMod 3847) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1842 : ZMod 3847)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3851 : Nat.Prime 3851 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3851 3850 1 2 [2, 5, 5, 7, 11]
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
    · change IsUnit ((2 : ZMod 3851) ^ 1925 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1925 : ZMod 3851)
      decide
    · change IsUnit ((2 : ZMod 3851) ^ 770 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3803 : ZMod 3851)
      decide
    · change IsUnit ((2 : ZMod 3851) ^ 770 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3803 : ZMod 3851)
      decide
    · change IsUnit ((2 : ZMod 3851) ^ 550 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2535 : ZMod 3851)
      decide
    · change IsUnit ((2 : ZMod 3851) ^ 350 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2407 : ZMod 3851)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3853 : Nat.Prime 3853 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3853 3852 1 2 [2, 2, 3, 3, 107]
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
    · change IsUnit ((2 : ZMod 3853) ^ 1926 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1926 : ZMod 3853)
      decide
    · change IsUnit ((2 : ZMod 3853) ^ 1926 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1926 : ZMod 3853)
      decide
    · change IsUnit ((2 : ZMod 3853) ^ 1284 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2948 : ZMod 3853)
      decide
    · change IsUnit ((2 : ZMod 3853) ^ 1284 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2948 : ZMod 3853)
      decide
    · change IsUnit ((2 : ZMod 3853) ^ 36 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1765 : ZMod 3853)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3863 : Nat.Prime 3863 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3863 3862 1 5 [2, 1931]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · change IsUnit ((5 : ZMod 3863) ^ 1931 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1931 : ZMod 3863)
      decide
    · change IsUnit ((5 : ZMod 3863) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (161 : ZMod 3863)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_3877 : Nat.Prime 3877 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 3877 3876 1 2 [2, 2, 3, 17, 19]
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
    · change IsUnit ((2 : ZMod 3877) ^ 1938 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1938 : ZMod 3877)
      decide
    · change IsUnit ((2 : ZMod 3877) ^ 1938 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1938 : ZMod 3877)
      decide
    · change IsUnit ((2 : ZMod 3877) ^ 1292 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1217 : ZMod 3877)
      decide
    · change IsUnit ((2 : ZMod 3877) ^ 228 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2439 : ZMod 3877)
      decide
    · change IsUnit ((2 : ZMod 3877) ^ 204 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3474 : ZMod 3877)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 3803) (q := 3821) (by exact lowPrime_3821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3821) (q := 3823) (by exact lowPrime_3823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3823) (q := 3833) (by exact lowPrime_3833) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3833) (q := 3847) (by exact lowPrime_3847) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3847) (q := 3851) (by exact lowPrime_3851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3851) (q := 3853) (by exact lowPrime_3853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3853) (q := 3863) (by exact lowPrime_3863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 3863) (q := 3877) (by exact lowPrime_3877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part01_chain :
    DusartPrimeRowsChain 3803 3877 dusartPrimeRows_3803_4672_part01 := by
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
