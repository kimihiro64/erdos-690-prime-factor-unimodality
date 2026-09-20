import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 152 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_13381 : Nat.Prime 13381 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13381 13380 1 10 [2, 2, 3, 5, 223]
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
    · change IsUnit ((10 : ZMod 13381) ^ 6690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6690 : ZMod 13381)
      decide
    · change IsUnit ((10 : ZMod 13381) ^ 6690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6690 : ZMod 13381)
      decide
    · change IsUnit ((10 : ZMod 13381) ^ 4460 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (467 : ZMod 13381)
      decide
    · change IsUnit ((10 : ZMod 13381) ^ 2676 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3923 : ZMod 13381)
      decide
    · change IsUnit ((10 : ZMod 13381) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12699 : ZMod 13381)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13397 : Nat.Prime 13397 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13397 13396 1 2 [2, 2, 17, 197]
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
    · change IsUnit ((2 : ZMod 13397) ^ 6698 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6698 : ZMod 13397)
      decide
    · change IsUnit ((2 : ZMod 13397) ^ 6698 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6698 : ZMod 13397)
      decide
    · change IsUnit ((2 : ZMod 13397) ^ 788 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7020 : ZMod 13397)
      decide
    · change IsUnit ((2 : ZMod 13397) ^ 68 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9128 : ZMod 13397)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13399 : Nat.Prime 13399 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13399 13398 1 3 [2, 3, 7, 11, 29]
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
    · change IsUnit ((3 : ZMod 13399) ^ 6699 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6699 : ZMod 13399)
      decide
    · change IsUnit ((3 : ZMod 13399) ^ 4466 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3492 : ZMod 13399)
      decide
    · change IsUnit ((3 : ZMod 13399) ^ 1914 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3265 : ZMod 13399)
      decide
    · change IsUnit ((3 : ZMod 13399) ^ 1218 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10715 : ZMod 13399)
      decide
    · change IsUnit ((3 : ZMod 13399) ^ 462 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (377 : ZMod 13399)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13411 : Nat.Prime 13411 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13411 13410 1 2 [2, 3, 3, 5, 149]
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
    · change IsUnit ((2 : ZMod 13411) ^ 6705 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6705 : ZMod 13411)
      decide
    · change IsUnit ((2 : ZMod 13411) ^ 4470 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12752 : ZMod 13411)
      decide
    · change IsUnit ((2 : ZMod 13411) ^ 4470 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12752 : ZMod 13411)
      decide
    · change IsUnit ((2 : ZMod 13411) ^ 2682 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (950 : ZMod 13411)
      decide
    · change IsUnit ((2 : ZMod 13411) ^ 90 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7784 : ZMod 13411)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13417 : Nat.Prime 13417 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13417 13416 1 5 [2, 2, 2, 3, 13, 43]
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
    · change IsUnit ((5 : ZMod 13417) ^ 6708 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6708 : ZMod 13417)
      decide
    · change IsUnit ((5 : ZMod 13417) ^ 6708 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6708 : ZMod 13417)
      decide
    · change IsUnit ((5 : ZMod 13417) ^ 6708 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6708 : ZMod 13417)
      decide
    · change IsUnit ((5 : ZMod 13417) ^ 4472 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8108 : ZMod 13417)
      decide
    · change IsUnit ((5 : ZMod 13417) ^ 1032 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10793 : ZMod 13417)
      decide
    · change IsUnit ((5 : ZMod 13417) ^ 312 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7977 : ZMod 13417)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13421 : Nat.Prime 13421 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13421 13420 1 10 [2, 2, 5, 11, 61]
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
    · change IsUnit ((10 : ZMod 13421) ^ 6710 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6710 : ZMod 13421)
      decide
    · change IsUnit ((10 : ZMod 13421) ^ 6710 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6710 : ZMod 13421)
      decide
    · change IsUnit ((10 : ZMod 13421) ^ 2684 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2125 : ZMod 13421)
      decide
    · change IsUnit ((10 : ZMod 13421) ^ 1220 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8581 : ZMod 13421)
      decide
    · change IsUnit ((10 : ZMod 13421) ^ 220 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12494 : ZMod 13421)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13441 : Nat.Prime 13441 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13441 13440 1 11 [2, 2, 2, 2, 2, 2, 2, 3, 5, 7]
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
    · change IsUnit ((11 : ZMod 13441) ^ 6720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6720 : ZMod 13441)
      decide
    · change IsUnit ((11 : ZMod 13441) ^ 6720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6720 : ZMod 13441)
      decide
    · change IsUnit ((11 : ZMod 13441) ^ 6720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6720 : ZMod 13441)
      decide
    · change IsUnit ((11 : ZMod 13441) ^ 6720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6720 : ZMod 13441)
      decide
    · change IsUnit ((11 : ZMod 13441) ^ 6720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6720 : ZMod 13441)
      decide
    · change IsUnit ((11 : ZMod 13441) ^ 6720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6720 : ZMod 13441)
      decide
    · change IsUnit ((11 : ZMod 13441) ^ 6720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6720 : ZMod 13441)
      decide
    · change IsUnit ((11 : ZMod 13441) ^ 4480 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8745 : ZMod 13441)
      decide
    · change IsUnit ((11 : ZMod 13441) ^ 2688 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1156 : ZMod 13441)
      decide
    · change IsUnit ((11 : ZMod 13441) ^ 1920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1552 : ZMod 13441)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13451 : Nat.Prime 13451 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13451 13450 1 2 [2, 5, 5, 269]
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
    · change IsUnit ((2 : ZMod 13451) ^ 6725 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6725 : ZMod 13451)
      decide
    · change IsUnit ((2 : ZMod 13451) ^ 2690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3205 : ZMod 13451)
      decide
    · change IsUnit ((2 : ZMod 13451) ^ 2690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3205 : ZMod 13451)
      decide
    · change IsUnit ((2 : ZMod 13451) ^ 50 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9663 : ZMod 13451)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13367) (q := 13381) (by exact lowPrime_13381) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13381) (q := 13397) (by exact lowPrime_13397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13397) (q := 13399) (by exact lowPrime_13399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13399) (q := 13411) (by exact lowPrime_13411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13411) (q := 13417) (by exact lowPrime_13417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13417) (q := 13421) (by exact lowPrime_13421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13421) (q := 13441) (by exact lowPrime_13441) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13441) (q := 13451) (by exact lowPrime_13451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part01_chain :
    DusartPrimeRowsChain 13367 13451 dusartPrimeRows_13367_14050_part01 := by
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
