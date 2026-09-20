import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 65 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_7349 : Nat.Prime 7349 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7349 7348 1 2 [2, 2, 11, 167]
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
    · change IsUnit ((2 : ZMod 7349) ^ 3674 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3674 : ZMod 7349)
      decide
    · change IsUnit ((2 : ZMod 7349) ^ 3674 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3674 : ZMod 7349)
      decide
    · change IsUnit ((2 : ZMod 7349) ^ 668 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4401 : ZMod 7349)
      decide
    · change IsUnit ((2 : ZMod 7349) ^ 44 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4288 : ZMod 7349)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7351 : Nat.Prime 7351 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7351 7350 1 6 [2, 3, 5, 5, 7, 7]
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
    · change IsUnit ((6 : ZMod 7351) ^ 3675 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3675 : ZMod 7351)
      decide
    · change IsUnit ((6 : ZMod 7351) ^ 2450 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7301 : ZMod 7351)
      decide
    · change IsUnit ((6 : ZMod 7351) ^ 1470 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1681 : ZMod 7351)
      decide
    · change IsUnit ((6 : ZMod 7351) ^ 1470 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1681 : ZMod 7351)
      decide
    · change IsUnit ((6 : ZMod 7351) ^ 1050 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (562 : ZMod 7351)
      decide
    · change IsUnit ((6 : ZMod 7351) ^ 1050 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (562 : ZMod 7351)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7369 : Nat.Prime 7369 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7369 7368 1 7 [2, 2, 2, 3, 307]
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
    · change IsUnit ((7 : ZMod 7369) ^ 3684 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3684 : ZMod 7369)
      decide
    · change IsUnit ((7 : ZMod 7369) ^ 3684 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3684 : ZMod 7369)
      decide
    · change IsUnit ((7 : ZMod 7369) ^ 3684 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3684 : ZMod 7369)
      decide
    · change IsUnit ((7 : ZMod 7369) ^ 2456 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3309 : ZMod 7369)
      decide
    · change IsUnit ((7 : ZMod 7369) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4219 : ZMod 7369)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7393 : Nat.Prime 7393 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7393 7392 1 5 [2, 2, 2, 2, 2, 3, 7, 11]
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
    · change IsUnit ((5 : ZMod 7393) ^ 3696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3696 : ZMod 7393)
      decide
    · change IsUnit ((5 : ZMod 7393) ^ 3696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3696 : ZMod 7393)
      decide
    · change IsUnit ((5 : ZMod 7393) ^ 3696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3696 : ZMod 7393)
      decide
    · change IsUnit ((5 : ZMod 7393) ^ 3696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3696 : ZMod 7393)
      decide
    · change IsUnit ((5 : ZMod 7393) ^ 3696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3696 : ZMod 7393)
      decide
    · change IsUnit ((5 : ZMod 7393) ^ 2464 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6820 : ZMod 7393)
      decide
    · change IsUnit ((5 : ZMod 7393) ^ 1056 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4639 : ZMod 7393)
      decide
    · change IsUnit ((5 : ZMod 7393) ^ 672 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1531 : ZMod 7393)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7411 : Nat.Prime 7411 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7411 7410 1 2 [2, 3, 5, 13, 19]
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
    · change IsUnit ((2 : ZMod 7411) ^ 3705 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3705 : ZMod 7411)
      decide
    · change IsUnit ((2 : ZMod 7411) ^ 2470 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7279 : ZMod 7411)
      decide
    · change IsUnit ((2 : ZMod 7411) ^ 1482 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6680 : ZMod 7411)
      decide
    · change IsUnit ((2 : ZMod 7411) ^ 570 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6714 : ZMod 7411)
      decide
    · change IsUnit ((2 : ZMod 7411) ^ 390 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6930 : ZMod 7411)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7417 : Nat.Prime 7417 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7417 7416 1 5 [2, 2, 2, 3, 3, 103]
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
    · change IsUnit ((5 : ZMod 7417) ^ 3708 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3708 : ZMod 7417)
      decide
    · change IsUnit ((5 : ZMod 7417) ^ 3708 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3708 : ZMod 7417)
      decide
    · change IsUnit ((5 : ZMod 7417) ^ 3708 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3708 : ZMod 7417)
      decide
    · change IsUnit ((5 : ZMod 7417) ^ 2472 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1701 : ZMod 7417)
      decide
    · change IsUnit ((5 : ZMod 7417) ^ 2472 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1701 : ZMod 7417)
      decide
    · change IsUnit ((5 : ZMod 7417) ^ 72 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6171 : ZMod 7417)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7433 : Nat.Prime 7433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7433 7432 1 3 [2, 2, 2, 929]
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
    · change IsUnit ((3 : ZMod 7433) ^ 3716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3716 : ZMod 7433)
      decide
    · change IsUnit ((3 : ZMod 7433) ^ 3716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3716 : ZMod 7433)
      decide
    · change IsUnit ((3 : ZMod 7433) ^ 3716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3716 : ZMod 7433)
      decide
    · change IsUnit ((3 : ZMod 7433) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (298 : ZMod 7433)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7451 : Nat.Prime 7451 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7451 7450 1 2 [2, 5, 5, 149]
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
    · change IsUnit ((2 : ZMod 7451) ^ 3725 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3725 : ZMod 7451)
      decide
    · change IsUnit ((2 : ZMod 7451) ^ 1490 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7046 : ZMod 7451)
      decide
    · change IsUnit ((2 : ZMod 7451) ^ 1490 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7046 : ZMod 7451)
      decide
    · change IsUnit ((2 : ZMod 7451) ^ 50 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1670 : ZMod 7451)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_7333_7716_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7707 (p := 7333) (q := 7349) (by exact lowPrime_7349) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7349) (q := 7351) (by exact lowPrime_7351) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7351) (q := 7369) (by exact lowPrime_7369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7369) (q := 7393) (by exact lowPrime_7393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7393) (q := 7411) (by exact lowPrime_7411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7411) (q := 7417) (by exact lowPrime_7417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7417) (q := 7433) (by exact lowPrime_7433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7707 (p := 7433) (q := 7451) (by exact lowPrime_7451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_7333_7716_part01_chain :
    DusartPrimeRowsChain 7333 7451 dusartPrimeRows_7333_7716_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · norm_num [dusartPrimeRow_of_explicit_7707]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · norm_num [dusartPrimeRow_of_explicit_7707]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · norm_num [dusartPrimeRow_of_explicit_7707]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · norm_num [dusartPrimeRow_of_explicit_7707]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · norm_num [dusartPrimeRow_of_explicit_7707]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · norm_num [dusartPrimeRow_of_explicit_7707]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · norm_num [dusartPrimeRow_of_explicit_7707]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · norm_num [dusartPrimeRow_of_explicit_7707]
                · apply DusartPrimeRowsChain.empty
                  norm_num
