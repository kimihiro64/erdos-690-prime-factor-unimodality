import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 230 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_21803 : Nat.Prime 21803 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21803 21802 1 2 [2, 11, 991]
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
    · change IsUnit ((2 : ZMod 21803) ^ 10901 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10901 : ZMod 21803)
      decide
    · change IsUnit ((2 : ZMod 21803) ^ 1982 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5777 : ZMod 21803)
      decide
    · change IsUnit ((2 : ZMod 21803) ^ 22 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10208 : ZMod 21803)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21817 : Nat.Prime 21817 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21817 21816 1 7 [2, 2, 2, 3, 3, 3, 101]
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
    · change IsUnit ((7 : ZMod 21817) ^ 10908 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10908 : ZMod 21817)
      decide
    · change IsUnit ((7 : ZMod 21817) ^ 10908 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10908 : ZMod 21817)
      decide
    · change IsUnit ((7 : ZMod 21817) ^ 10908 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10908 : ZMod 21817)
      decide
    · change IsUnit ((7 : ZMod 21817) ^ 7272 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (21003 : ZMod 21817)
      decide
    · change IsUnit ((7 : ZMod 21817) ^ 7272 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (21003 : ZMod 21817)
      decide
    · change IsUnit ((7 : ZMod 21817) ^ 7272 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (21003 : ZMod 21817)
      decide
    · change IsUnit ((7 : ZMod 21817) ^ 216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2906 : ZMod 21817)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21821 : Nat.Prime 21821 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21821 21820 1 2 [2, 2, 5, 1091]
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
    · change IsUnit ((2 : ZMod 21821) ^ 10910 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10910 : ZMod 21821)
      decide
    · change IsUnit ((2 : ZMod 21821) ^ 10910 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10910 : ZMod 21821)
      decide
    · change IsUnit ((2 : ZMod 21821) ^ 4364 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7500 : ZMod 21821)
      decide
    · change IsUnit ((2 : ZMod 21821) ^ 20 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14940 : ZMod 21821)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21839 : Nat.Prime 21839 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21839 21838 1 11 [2, 61, 179]
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
    · change IsUnit ((11 : ZMod 21839) ^ 10919 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10919 : ZMod 21839)
      decide
    · change IsUnit ((11 : ZMod 21839) ^ 358 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7033 : ZMod 21839)
      decide
    · change IsUnit ((11 : ZMod 21839) ^ 122 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8208 : ZMod 21839)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21841 : Nat.Prime 21841 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21841 21840 1 11 [2, 2, 2, 2, 3, 5, 7, 13]
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
    · change IsUnit ((11 : ZMod 21841) ^ 10920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10920 : ZMod 21841)
      decide
    · change IsUnit ((11 : ZMod 21841) ^ 10920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10920 : ZMod 21841)
      decide
    · change IsUnit ((11 : ZMod 21841) ^ 10920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10920 : ZMod 21841)
      decide
    · change IsUnit ((11 : ZMod 21841) ^ 10920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10920 : ZMod 21841)
      decide
    · change IsUnit ((11 : ZMod 21841) ^ 7280 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11717 : ZMod 21841)
      decide
    · change IsUnit ((11 : ZMod 21841) ^ 4368 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7116 : ZMod 21841)
      decide
    · change IsUnit ((11 : ZMod 21841) ^ 3120 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6835 : ZMod 21841)
      decide
    · change IsUnit ((11 : ZMod 21841) ^ 1680 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5776 : ZMod 21841)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21851 : Nat.Prime 21851 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21851 21850 1 6 [2, 5, 5, 19, 23]
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
    · change IsUnit ((6 : ZMod 21851) ^ 10925 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10925 : ZMod 21851)
      decide
    · change IsUnit ((6 : ZMod 21851) ^ 4370 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16804 : ZMod 21851)
      decide
    · change IsUnit ((6 : ZMod 21851) ^ 4370 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16804 : ZMod 21851)
      decide
    · change IsUnit ((6 : ZMod 21851) ^ 1150 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3402 : ZMod 21851)
      decide
    · change IsUnit ((6 : ZMod 21851) ^ 950 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2445 : ZMod 21851)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21859 : Nat.Prime 21859 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21859 21858 1 2 [2, 3, 3643]
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
    · change IsUnit ((2 : ZMod 21859) ^ 10929 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10929 : ZMod 21859)
      decide
    · change IsUnit ((2 : ZMod 21859) ^ 7286 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19322 : ZMod 21859)
      decide
    · change IsUnit ((2 : ZMod 21859) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11103 : ZMod 21859)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21863 : Nat.Prime 21863 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21863 21862 1 5 [2, 17, 643]
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
    · change IsUnit ((5 : ZMod 21863) ^ 10931 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10931 : ZMod 21863)
      decide
    · change IsUnit ((5 : ZMod 21863) ^ 1286 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8620 : ZMod 21863)
      decide
    · change IsUnit ((5 : ZMod 21863) ^ 34 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4355 : ZMod 21863)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21799) (q := 21803) (by exact lowPrime_21803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21803) (q := 21817) (by exact lowPrime_21817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21817) (q := 21821) (by exact lowPrime_21821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21821) (q := 21839) (by exact lowPrime_21839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21839) (q := 21841) (by exact lowPrime_21841) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21841) (q := 21851) (by exact lowPrime_21851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21851) (q := 21859) (by exact lowPrime_21859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21859) (q := 21863) (by exact lowPrime_21863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part12_chain :
    DusartPrimeRowsChain 21799 21863 dusartPrimeRows_20959_22026_part12 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num
