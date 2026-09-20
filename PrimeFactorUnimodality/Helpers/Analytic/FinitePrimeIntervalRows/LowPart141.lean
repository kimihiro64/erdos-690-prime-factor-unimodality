import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 141 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_12589 : Nat.Prime 12589 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12589 12588 1 2 [2, 2, 3, 1049]
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
    · change IsUnit ((2 : ZMod 12589) ^ 6294 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6294 : ZMod 12589)
      decide
    · change IsUnit ((2 : ZMod 12589) ^ 6294 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6294 : ZMod 12589)
      decide
    · change IsUnit ((2 : ZMod 12589) ^ 4196 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5975 : ZMod 12589)
      decide
    · change IsUnit ((2 : ZMod 12589) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11885 : ZMod 12589)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12601 : Nat.Prime 12601 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12601 12600 1 11 [2, 2, 2, 3, 3, 5, 5, 7]
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
    · change IsUnit ((11 : ZMod 12601) ^ 6300 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6300 : ZMod 12601)
      decide
    · change IsUnit ((11 : ZMod 12601) ^ 6300 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6300 : ZMod 12601)
      decide
    · change IsUnit ((11 : ZMod 12601) ^ 6300 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6300 : ZMod 12601)
      decide
    · change IsUnit ((11 : ZMod 12601) ^ 4200 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (282 : ZMod 12601)
      decide
    · change IsUnit ((11 : ZMod 12601) ^ 4200 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (282 : ZMod 12601)
      decide
    · change IsUnit ((11 : ZMod 12601) ^ 2520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11301 : ZMod 12601)
      decide
    · change IsUnit ((11 : ZMod 12601) ^ 2520 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11301 : ZMod 12601)
      decide
    · change IsUnit ((11 : ZMod 12601) ^ 1800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10631 : ZMod 12601)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12611 : Nat.Prime 12611 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12611 12610 1 2 [2, 5, 13, 97]
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
    · change IsUnit ((2 : ZMod 12611) ^ 6305 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6305 : ZMod 12611)
      decide
    · change IsUnit ((2 : ZMod 12611) ^ 2522 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5112 : ZMod 12611)
      decide
    · change IsUnit ((2 : ZMod 12611) ^ 970 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7453 : ZMod 12611)
      decide
    · change IsUnit ((2 : ZMod 12611) ^ 130 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7749 : ZMod 12611)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12613 : Nat.Prime 12613 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12613 12612 1 2 [2, 2, 3, 1051]
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
    · change IsUnit ((2 : ZMod 12613) ^ 6306 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6306 : ZMod 12613)
      decide
    · change IsUnit ((2 : ZMod 12613) ^ 6306 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6306 : ZMod 12613)
      decide
    · change IsUnit ((2 : ZMod 12613) ^ 4204 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6029 : ZMod 12613)
      decide
    · change IsUnit ((2 : ZMod 12613) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11344 : ZMod 12613)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12619 : Nat.Prime 12619 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12619 12618 1 2 [2, 3, 3, 701]
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
    · change IsUnit ((2 : ZMod 12619) ^ 6309 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6309 : ZMod 12619)
      decide
    · change IsUnit ((2 : ZMod 12619) ^ 4206 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5464 : ZMod 12619)
      decide
    · change IsUnit ((2 : ZMod 12619) ^ 4206 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5464 : ZMod 12619)
      decide
    · change IsUnit ((2 : ZMod 12619) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2735 : ZMod 12619)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12637 : Nat.Prime 12637 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12637 12636 1 2 [2, 2, 3, 3, 3, 3, 3, 13]
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
    · change IsUnit ((2 : ZMod 12637) ^ 6318 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6318 : ZMod 12637)
      decide
    · change IsUnit ((2 : ZMod 12637) ^ 6318 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6318 : ZMod 12637)
      decide
    · change IsUnit ((2 : ZMod 12637) ^ 4212 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2024 : ZMod 12637)
      decide
    · change IsUnit ((2 : ZMod 12637) ^ 4212 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2024 : ZMod 12637)
      decide
    · change IsUnit ((2 : ZMod 12637) ^ 4212 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2024 : ZMod 12637)
      decide
    · change IsUnit ((2 : ZMod 12637) ^ 4212 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2024 : ZMod 12637)
      decide
    · change IsUnit ((2 : ZMod 12637) ^ 4212 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2024 : ZMod 12637)
      decide
    · change IsUnit ((2 : ZMod 12637) ^ 972 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8630 : ZMod 12637)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12641 : Nat.Prime 12641 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12641 12640 1 3 [2, 2, 2, 2, 2, 5, 79]
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
    · change IsUnit ((3 : ZMod 12641) ^ 6320 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6320 : ZMod 12641)
      decide
    · change IsUnit ((3 : ZMod 12641) ^ 6320 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6320 : ZMod 12641)
      decide
    · change IsUnit ((3 : ZMod 12641) ^ 6320 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6320 : ZMod 12641)
      decide
    · change IsUnit ((3 : ZMod 12641) ^ 6320 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6320 : ZMod 12641)
      decide
    · change IsUnit ((3 : ZMod 12641) ^ 6320 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6320 : ZMod 12641)
      decide
    · change IsUnit ((3 : ZMod 12641) ^ 2528 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3382 : ZMod 12641)
      decide
    · change IsUnit ((3 : ZMod 12641) ^ 160 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1581 : ZMod 12641)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12647 : Nat.Prime 12647 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12647 12646 1 5 [2, 6323]
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
    · change IsUnit ((5 : ZMod 12647) ^ 6323 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6323 : ZMod 12647)
      decide
    · change IsUnit ((5 : ZMod 12647) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (527 : ZMod 12647)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12583) (q := 12589) (by exact lowPrime_12589) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12589) (q := 12601) (by exact lowPrime_12601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12601) (q := 12611) (by exact lowPrime_12611) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12611) (q := 12613) (by exact lowPrime_12613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12613) (q := 12619) (by exact lowPrime_12619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12619) (q := 12637) (by exact lowPrime_12637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12637) (q := 12641) (by exact lowPrime_12641) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12641) (q := 12647) (by exact lowPrime_12647) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part08_chain :
    DusartPrimeRowsChain 12583 12647 dusartPrimeRows_12097_12712_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num
