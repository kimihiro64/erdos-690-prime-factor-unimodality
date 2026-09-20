import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 56 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_6781 : Nat.Prime 6781 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6781 6780 1 2 [2, 2, 3, 5, 113]
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
    · change IsUnit ((2 : ZMod 6781) ^ 3390 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3390 : ZMod 6781)
      decide
    · change IsUnit ((2 : ZMod 6781) ^ 3390 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3390 : ZMod 6781)
      decide
    · change IsUnit ((2 : ZMod 6781) ^ 2260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5805 : ZMod 6781)
      decide
    · change IsUnit ((2 : ZMod 6781) ^ 1356 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2015 : ZMod 6781)
      decide
    · change IsUnit ((2 : ZMod 6781) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4281 : ZMod 6781)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6791 : Nat.Prime 6791 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6791 6790 1 7 [2, 5, 7, 97]
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
    · change IsUnit ((7 : ZMod 6791) ^ 3395 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3395 : ZMod 6791)
      decide
    · change IsUnit ((7 : ZMod 6791) ^ 1358 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2688 : ZMod 6791)
      decide
    · change IsUnit ((7 : ZMod 6791) ^ 970 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (208 : ZMod 6791)
      decide
    · change IsUnit ((7 : ZMod 6791) ^ 70 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6748 : ZMod 6791)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6793 : Nat.Prime 6793 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6793 6792 1 10 [2, 2, 2, 3, 283]
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
    · change IsUnit ((10 : ZMod 6793) ^ 3396 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3396 : ZMod 6793)
      decide
    · change IsUnit ((10 : ZMod 6793) ^ 3396 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3396 : ZMod 6793)
      decide
    · change IsUnit ((10 : ZMod 6793) ^ 3396 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3396 : ZMod 6793)
      decide
    · change IsUnit ((10 : ZMod 6793) ^ 2264 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6403 : ZMod 6793)
      decide
    · change IsUnit ((10 : ZMod 6793) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3816 : ZMod 6793)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6803 : Nat.Prime 6803 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6803 6802 1 2 [2, 19, 179]
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
    · change IsUnit ((2 : ZMod 6803) ^ 3401 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3401 : ZMod 6803)
      decide
    · change IsUnit ((2 : ZMod 6803) ^ 358 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (585 : ZMod 6803)
      decide
    · change IsUnit ((2 : ZMod 6803) ^ 38 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3982 : ZMod 6803)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6823 : Nat.Prime 6823 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6823 6822 1 3 [2, 3, 3, 379]
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
    · change IsUnit ((3 : ZMod 6823) ^ 3411 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3411 : ZMod 6823)
      decide
    · change IsUnit ((3 : ZMod 6823) ^ 2274 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3169 : ZMod 6823)
      decide
    · change IsUnit ((3 : ZMod 6823) ^ 2274 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3169 : ZMod 6823)
      decide
    · change IsUnit ((3 : ZMod 6823) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3504 : ZMod 6823)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6827 : Nat.Prime 6827 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6827 6826 1 2 [2, 3413]
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
    · change IsUnit ((2 : ZMod 6827) ^ 3413 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3413 : ZMod 6827)
      decide
    · change IsUnit ((2 : ZMod 6827) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2276 : ZMod 6827)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6829 : Nat.Prime 6829 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6829 6828 1 2 [2, 2, 3, 569]
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
    · change IsUnit ((2 : ZMod 6829) ^ 3414 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3414 : ZMod 6829)
      decide
    · change IsUnit ((2 : ZMod 6829) ^ 3414 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3414 : ZMod 6829)
      decide
    · change IsUnit ((2 : ZMod 6829) ^ 2276 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2031 : ZMod 6829)
      decide
    · change IsUnit ((2 : ZMod 6829) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2845 : ZMod 6829)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6833 : Nat.Prime 6833 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6833 6832 1 3 [2, 2, 2, 2, 7, 61]
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
    · change IsUnit ((3 : ZMod 6833) ^ 3416 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3416 : ZMod 6833)
      decide
    · change IsUnit ((3 : ZMod 6833) ^ 3416 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3416 : ZMod 6833)
      decide
    · change IsUnit ((3 : ZMod 6833) ^ 3416 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3416 : ZMod 6833)
      decide
    · change IsUnit ((3 : ZMod 6833) ^ 3416 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3416 : ZMod 6833)
      decide
    · change IsUnit ((3 : ZMod 6833) ^ 976 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6811 : ZMod 6833)
      decide
    · change IsUnit ((3 : ZMod 6833) ^ 112 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2179 : ZMod 6833)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6637_6976_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6974 (p := 6779) (q := 6781) (by exact lowPrime_6781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6781) (q := 6791) (by exact lowPrime_6791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6791) (q := 6793) (by exact lowPrime_6793) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6793) (q := 6803) (by exact lowPrime_6803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6803) (q := 6823) (by exact lowPrime_6823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6823) (q := 6827) (by exact lowPrime_6827) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6827) (q := 6829) (by exact lowPrime_6829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6974 (p := 6829) (q := 6833) (by exact lowPrime_6833) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6637_6976_part03_chain :
    DusartPrimeRowsChain 6779 6833 dusartPrimeRows_6637_6976_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · norm_num [dusartPrimeRow_of_explicit_6974]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6974]
    · norm_num [dusartPrimeRow_of_explicit_6974]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6974]
      · norm_num [dusartPrimeRow_of_explicit_6974]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6974]
        · norm_num [dusartPrimeRow_of_explicit_6974]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6974]
          · norm_num [dusartPrimeRow_of_explicit_6974]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6974]
            · norm_num [dusartPrimeRow_of_explicit_6974]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6974]
              · norm_num [dusartPrimeRow_of_explicit_6974]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6974]
                · norm_num [dusartPrimeRow_of_explicit_6974]
                · apply DusartPrimeRowsChain.empty
                  norm_num
