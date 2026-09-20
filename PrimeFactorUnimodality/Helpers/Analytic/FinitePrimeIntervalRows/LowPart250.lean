import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 250 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_19309 : Nat.Prime 19309 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19309 19308 1 6 [2, 2, 3, 1609]
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
    · change IsUnit ((6 : ZMod 19309) ^ 9654 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9654 : ZMod 19309)
      decide
    · change IsUnit ((6 : ZMod 19309) ^ 9654 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9654 : ZMod 19309)
      decide
    · change IsUnit ((6 : ZMod 19309) ^ 6436 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9410 : ZMod 19309)
      decide
    · change IsUnit ((6 : ZMod 19309) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13020 : ZMod 19309)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19319 : Nat.Prime 19319 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19319 19318 1 11 [2, 13, 743]
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
    · change IsUnit ((11 : ZMod 19319) ^ 9659 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9659 : ZMod 19319)
      decide
    · change IsUnit ((11 : ZMod 19319) ^ 1486 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10676 : ZMod 19319)
      decide
    · change IsUnit ((11 : ZMod 19319) ^ 26 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13989 : ZMod 19319)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19333 : Nat.Prime 19333 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19333 19332 1 2 [2, 2, 3, 3, 3, 179]
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
    · change IsUnit ((2 : ZMod 19333) ^ 9666 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9666 : ZMod 19333)
      decide
    · change IsUnit ((2 : ZMod 19333) ^ 9666 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9666 : ZMod 19333)
      decide
    · change IsUnit ((2 : ZMod 19333) ^ 6444 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1599 : ZMod 19333)
      decide
    · change IsUnit ((2 : ZMod 19333) ^ 6444 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1599 : ZMod 19333)
      decide
    · change IsUnit ((2 : ZMod 19333) ^ 6444 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1599 : ZMod 19333)
      decide
    · change IsUnit ((2 : ZMod 19333) ^ 108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2472 : ZMod 19333)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19373 : Nat.Prime 19373 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19373 19372 1 2 [2, 2, 29, 167]
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
    · change IsUnit ((2 : ZMod 19373) ^ 9686 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9686 : ZMod 19373)
      decide
    · change IsUnit ((2 : ZMod 19373) ^ 9686 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9686 : ZMod 19373)
      decide
    · change IsUnit ((2 : ZMod 19373) ^ 668 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7830 : ZMod 19373)
      decide
    · change IsUnit ((2 : ZMod 19373) ^ 116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6058 : ZMod 19373)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19379 : Nat.Prime 19379 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19379 19378 1 2 [2, 9689]
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
    · change IsUnit ((2 : ZMod 19379) ^ 9689 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9689 : ZMod 19379)
      decide
    · change IsUnit ((2 : ZMod 19379) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6460 : ZMod 19379)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19381 : Nat.Prime 19381 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19381 19380 1 7 [2, 2, 3, 5, 17, 19]
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
    · change IsUnit ((7 : ZMod 19381) ^ 9690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9690 : ZMod 19381)
      decide
    · change IsUnit ((7 : ZMod 19381) ^ 9690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9690 : ZMod 19381)
      decide
    · change IsUnit ((7 : ZMod 19381) ^ 6460 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10401 : ZMod 19381)
      decide
    · change IsUnit ((7 : ZMod 19381) ^ 3876 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4122 : ZMod 19381)
      decide
    · change IsUnit ((7 : ZMod 19381) ^ 1140 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12635 : ZMod 19381)
      decide
    · change IsUnit ((7 : ZMod 19381) ^ 1020 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (241 : ZMod 19381)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19387 : Nat.Prime 19387 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19387 19386 1 2 [2, 3, 3, 3, 359]
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
    · change IsUnit ((2 : ZMod 19387) ^ 9693 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9693 : ZMod 19387)
      decide
    · change IsUnit ((2 : ZMod 19387) ^ 6462 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11875 : ZMod 19387)
      decide
    · change IsUnit ((2 : ZMod 19387) ^ 6462 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11875 : ZMod 19387)
      decide
    · change IsUnit ((2 : ZMod 19387) ^ 6462 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11875 : ZMod 19387)
      decide
    · change IsUnit ((2 : ZMod 19387) ^ 54 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16619 : ZMod 19387)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19391 : Nat.Prime 19391 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19391 19390 1 11 [2, 5, 7, 277]
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
    · change IsUnit ((11 : ZMod 19391) ^ 9695 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9695 : ZMod 19391)
      decide
    · change IsUnit ((11 : ZMod 19391) ^ 3878 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9063 : ZMod 19391)
      decide
    · change IsUnit ((11 : ZMod 19391) ^ 2770 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7024 : ZMod 19391)
      decide
    · change IsUnit ((11 : ZMod 19391) ^ 70 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4910 : ZMod 19391)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19301) (q := 19309) (by exact lowPrime_19309) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19309) (q := 19319) (by exact lowPrime_19319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19319) (q := 19333) (by exact lowPrime_19333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19333) (q := 19373) (by exact lowPrime_19373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19373) (q := 19379) (by exact lowPrime_19379) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19379) (q := 19381) (by exact lowPrime_19381) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19381) (q := 19387) (by exact lowPrime_19387) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19387) (q := 19391) (by exact lowPrime_19391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part05_chain :
    DusartPrimeRowsChain 19301 19391 dusartPrimeRows_18959_19936_part05 := by
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
