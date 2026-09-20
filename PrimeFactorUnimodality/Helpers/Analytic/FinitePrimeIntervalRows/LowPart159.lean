import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 159 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_13903 : Nat.Prime 13903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13903 13902 1 3 [2, 3, 7, 331]
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
    · change IsUnit ((3 : ZMod 13903) ^ 6951 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6951 : ZMod 13903)
      decide
    · change IsUnit ((3 : ZMod 13903) ^ 4634 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4415 : ZMod 13903)
      decide
    · change IsUnit ((3 : ZMod 13903) ^ 1986 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8438 : ZMod 13903)
      decide
    · change IsUnit ((3 : ZMod 13903) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3786 : ZMod 13903)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13907 : Nat.Prime 13907 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13907 13906 1 2 [2, 17, 409]
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
    · change IsUnit ((2 : ZMod 13907) ^ 6953 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6953 : ZMod 13907)
      decide
    · change IsUnit ((2 : ZMod 13907) ^ 818 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (563 : ZMod 13907)
      decide
    · change IsUnit ((2 : ZMod 13907) ^ 34 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13516 : ZMod 13907)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13913 : Nat.Prime 13913 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13913 13912 1 3 [2, 2, 2, 37, 47]
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
    · change IsUnit ((3 : ZMod 13913) ^ 6956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6956 : ZMod 13913)
      decide
    · change IsUnit ((3 : ZMod 13913) ^ 6956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6956 : ZMod 13913)
      decide
    · change IsUnit ((3 : ZMod 13913) ^ 6956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6956 : ZMod 13913)
      decide
    · change IsUnit ((3 : ZMod 13913) ^ 376 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13008 : ZMod 13913)
      decide
    · change IsUnit ((3 : ZMod 13913) ^ 296 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9566 : ZMod 13913)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13921 : Nat.Prime 13921 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13921 13920 1 7 [2, 2, 2, 2, 2, 3, 5, 29]
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
    · change IsUnit ((7 : ZMod 13921) ^ 6960 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6960 : ZMod 13921)
      decide
    · change IsUnit ((7 : ZMod 13921) ^ 6960 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6960 : ZMod 13921)
      decide
    · change IsUnit ((7 : ZMod 13921) ^ 6960 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6960 : ZMod 13921)
      decide
    · change IsUnit ((7 : ZMod 13921) ^ 6960 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6960 : ZMod 13921)
      decide
    · change IsUnit ((7 : ZMod 13921) ^ 6960 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6960 : ZMod 13921)
      decide
    · change IsUnit ((7 : ZMod 13921) ^ 4640 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12931 : ZMod 13921)
      decide
    · change IsUnit ((7 : ZMod 13921) ^ 2784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6717 : ZMod 13921)
      decide
    · change IsUnit ((7 : ZMod 13921) ^ 480 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (648 : ZMod 13921)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13931 : Nat.Prime 13931 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13931 13930 1 2 [2, 5, 7, 199]
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
    · change IsUnit ((2 : ZMod 13931) ^ 6965 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6965 : ZMod 13931)
      decide
    · change IsUnit ((2 : ZMod 13931) ^ 2786 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6123 : ZMod 13931)
      decide
    · change IsUnit ((2 : ZMod 13931) ^ 1990 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4477 : ZMod 13931)
      decide
    · change IsUnit ((2 : ZMod 13931) ^ 70 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8941 : ZMod 13931)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13933 : Nat.Prime 13933 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13933 13932 1 2 [2, 2, 3, 3, 3, 3, 43]
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
    · change IsUnit ((2 : ZMod 13933) ^ 6966 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6966 : ZMod 13933)
      decide
    · change IsUnit ((2 : ZMod 13933) ^ 6966 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6966 : ZMod 13933)
      decide
    · change IsUnit ((2 : ZMod 13933) ^ 4644 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (711 : ZMod 13933)
      decide
    · change IsUnit ((2 : ZMod 13933) ^ 4644 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (711 : ZMod 13933)
      decide
    · change IsUnit ((2 : ZMod 13933) ^ 4644 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (711 : ZMod 13933)
      decide
    · change IsUnit ((2 : ZMod 13933) ^ 4644 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (711 : ZMod 13933)
      decide
    · change IsUnit ((2 : ZMod 13933) ^ 324 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5120 : ZMod 13933)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13963 : Nat.Prime 13963 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13963 13962 1 3 [2, 3, 13, 179]
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
    · change IsUnit ((3 : ZMod 13963) ^ 6981 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6981 : ZMod 13963)
      decide
    · change IsUnit ((3 : ZMod 13963) ^ 4654 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (180 : ZMod 13963)
      decide
    · change IsUnit ((3 : ZMod 13963) ^ 1074 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1535 : ZMod 13963)
      decide
    · change IsUnit ((3 : ZMod 13963) ^ 78 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10323 : ZMod 13963)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13967 : Nat.Prime 13967 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13967 13966 1 5 [2, 6983]
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
    · change IsUnit ((5 : ZMod 13967) ^ 6983 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6983 : ZMod 13967)
      decide
    · change IsUnit ((5 : ZMod 13967) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (582 : ZMod 13967)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13901) (q := 13903) (by exact lowPrime_13903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13903) (q := 13907) (by exact lowPrime_13907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13907) (q := 13913) (by exact lowPrime_13913) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13913) (q := 13921) (by exact lowPrime_13921) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13921) (q := 13931) (by exact lowPrime_13931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13931) (q := 13933) (by exact lowPrime_13933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13933) (q := 13963) (by exact lowPrime_13963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13963) (q := 13967) (by exact lowPrime_13967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part08_chain :
    DusartPrimeRowsChain 13901 13967 dusartPrimeRows_13367_14050_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num
