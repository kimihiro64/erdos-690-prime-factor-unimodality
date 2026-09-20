import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 35 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_5441 : Nat.Prime 5441 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5441 5440 1 3 [2, 2, 2, 2, 2, 2, 5, 17]
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
    · change IsUnit ((3 : ZMod 5441) ^ 2720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2720 : ZMod 5441)
      decide
    · change IsUnit ((3 : ZMod 5441) ^ 2720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2720 : ZMod 5441)
      decide
    · change IsUnit ((3 : ZMod 5441) ^ 2720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2720 : ZMod 5441)
      decide
    · change IsUnit ((3 : ZMod 5441) ^ 2720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2720 : ZMod 5441)
      decide
    · change IsUnit ((3 : ZMod 5441) ^ 2720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2720 : ZMod 5441)
      decide
    · change IsUnit ((3 : ZMod 5441) ^ 2720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2720 : ZMod 5441)
      decide
    · change IsUnit ((3 : ZMod 5441) ^ 1088 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2168 : ZMod 5441)
      decide
    · change IsUnit ((3 : ZMod 5441) ^ 320 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4226 : ZMod 5441)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5443 : Nat.Prime 5443 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5443 5442 1 2 [2, 3, 907]
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
    · change IsUnit ((2 : ZMod 5443) ^ 2721 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2721 : ZMod 5443)
      decide
    · change IsUnit ((2 : ZMod 5443) ^ 1814 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (951 : ZMod 5443)
      decide
    · change IsUnit ((2 : ZMod 5443) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (432 : ZMod 5443)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5449 : Nat.Prime 5449 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5449 5448 1 7 [2, 2, 2, 3, 227]
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
    · change IsUnit ((7 : ZMod 5449) ^ 2724 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2724 : ZMod 5449)
      decide
    · change IsUnit ((7 : ZMod 5449) ^ 2724 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2724 : ZMod 5449)
      decide
    · change IsUnit ((7 : ZMod 5449) ^ 2724 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2724 : ZMod 5449)
      decide
    · change IsUnit ((7 : ZMod 5449) ^ 1816 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (491 : ZMod 5449)
      decide
    · change IsUnit ((7 : ZMod 5449) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3591 : ZMod 5449)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5471 : Nat.Prime 5471 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5471 5470 1 7 [2, 5, 547]
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
    · change IsUnit ((7 : ZMod 5471) ^ 2735 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2735 : ZMod 5471)
      decide
    · change IsUnit ((7 : ZMod 5471) ^ 1094 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (285 : ZMod 5471)
      decide
    · change IsUnit ((7 : ZMod 5471) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4140 : ZMod 5471)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5477 : Nat.Prime 5477 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5477 5476 1 2 [2, 2, 37, 37]
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
    · change IsUnit ((2 : ZMod 5477) ^ 2738 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2738 : ZMod 5477)
      decide
    · change IsUnit ((2 : ZMod 5477) ^ 2738 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2738 : ZMod 5477)
      decide
    · change IsUnit ((2 : ZMod 5477) ^ 148 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4911 : ZMod 5477)
      decide
    · change IsUnit ((2 : ZMod 5477) ^ 148 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4911 : ZMod 5477)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5479 : Nat.Prime 5479 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5479 5478 1 3 [2, 3, 11, 83]
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
    · change IsUnit ((3 : ZMod 5479) ^ 2739 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2739 : ZMod 5479)
      decide
    · change IsUnit ((3 : ZMod 5479) ^ 1826 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (925 : ZMod 5479)
      decide
    · change IsUnit ((3 : ZMod 5479) ^ 498 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3119 : ZMod 5479)
      decide
    · change IsUnit ((3 : ZMod 5479) ^ 66 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4626 : ZMod 5479)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5483 : Nat.Prime 5483 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5483 5482 1 2 [2, 2741]
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
    · change IsUnit ((2 : ZMod 5483) ^ 2741 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2741 : ZMod 5483)
      decide
    · change IsUnit ((2 : ZMod 5483) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1828 : ZMod 5483)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5501 : Nat.Prime 5501 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5501 5500 1 2 [2, 2, 5, 5, 5, 11]
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
    · change IsUnit ((2 : ZMod 5501) ^ 2750 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2750 : ZMod 5501)
      decide
    · change IsUnit ((2 : ZMod 5501) ^ 2750 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2750 : ZMod 5501)
      decide
    · change IsUnit ((2 : ZMod 5501) ^ 1100 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1127 : ZMod 5501)
      decide
    · change IsUnit ((2 : ZMod 5501) ^ 1100 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1127 : ZMod 5501)
      decide
    · change IsUnit ((2 : ZMod 5501) ^ 1100 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1127 : ZMod 5501)
      decide
    · change IsUnit ((2 : ZMod 5501) ^ 500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2645 : ZMod 5501)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5437_5710_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5710 (p := 5437) (q := 5441) (by exact lowPrime_5441) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5441) (q := 5443) (by exact lowPrime_5443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5443) (q := 5449) (by exact lowPrime_5449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5449) (q := 5471) (by exact lowPrime_5471) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5471) (q := 5477) (by exact lowPrime_5477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5477) (q := 5479) (by exact lowPrime_5479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5479) (q := 5483) (by exact lowPrime_5483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5710 (p := 5483) (q := 5501) (by exact lowPrime_5501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5437_5710_part01_chain :
    DusartPrimeRowsChain 5437 5501 dusartPrimeRows_5437_5710_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · norm_num [dusartPrimeRow_of_explicit_5710]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · norm_num [dusartPrimeRow_of_explicit_5710]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5710]
      · norm_num [dusartPrimeRow_of_explicit_5710]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5710]
        · norm_num [dusartPrimeRow_of_explicit_5710]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5710]
          · norm_num [dusartPrimeRow_of_explicit_5710]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5710]
            · norm_num [dusartPrimeRow_of_explicit_5710]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5710]
              · norm_num [dusartPrimeRow_of_explicit_5710]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5710]
                · norm_num [dusartPrimeRow_of_explicit_5710]
                · apply DusartPrimeRowsChain.empty
                  norm_num
