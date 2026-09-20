import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 224 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_21377 : Nat.Prime 21377 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21377 21376 1 3 [2, 2, 2, 2, 2, 2, 2, 167]
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
    · change IsUnit ((3 : ZMod 21377) ^ 10688 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10688 : ZMod 21377)
      decide
    · change IsUnit ((3 : ZMod 21377) ^ 10688 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10688 : ZMod 21377)
      decide
    · change IsUnit ((3 : ZMod 21377) ^ 10688 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10688 : ZMod 21377)
      decide
    · change IsUnit ((3 : ZMod 21377) ^ 10688 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10688 : ZMod 21377)
      decide
    · change IsUnit ((3 : ZMod 21377) ^ 10688 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10688 : ZMod 21377)
      decide
    · change IsUnit ((3 : ZMod 21377) ^ 10688 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10688 : ZMod 21377)
      decide
    · change IsUnit ((3 : ZMod 21377) ^ 10688 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10688 : ZMod 21377)
      decide
    · change IsUnit ((3 : ZMod 21377) ^ 128 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17256 : ZMod 21377)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21379 : Nat.Prime 21379 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21379 21378 1 2 [2, 3, 7, 509]
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
    · change IsUnit ((2 : ZMod 21379) ^ 10689 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10689 : ZMod 21379)
      decide
    · change IsUnit ((2 : ZMod 21379) ^ 7126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19885 : ZMod 21379)
      decide
    · change IsUnit ((2 : ZMod 21379) ^ 3054 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13349 : ZMod 21379)
      decide
    · change IsUnit ((2 : ZMod 21379) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1728 : ZMod 21379)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21383 : Nat.Prime 21383 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21383 21382 1 5 [2, 10691]
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
    · change IsUnit ((5 : ZMod 21383) ^ 10691 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10691 : ZMod 21383)
      decide
    · change IsUnit ((5 : ZMod 21383) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (891 : ZMod 21383)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21391 : Nat.Prime 21391 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21391 21390 1 6 [2, 3, 5, 23, 31]
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
    · change IsUnit ((6 : ZMod 21391) ^ 10695 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10695 : ZMod 21391)
      decide
    · change IsUnit ((6 : ZMod 21391) ^ 7130 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7838 : ZMod 21391)
      decide
    · change IsUnit ((6 : ZMod 21391) ^ 4278 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7379 : ZMod 21391)
      decide
    · change IsUnit ((6 : ZMod 21391) ^ 930 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15527 : ZMod 21391)
      decide
    · change IsUnit ((6 : ZMod 21391) ^ 690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18913 : ZMod 21391)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21397 : Nat.Prime 21397 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21397 21396 1 2 [2, 2, 3, 1783]
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
    · change IsUnit ((2 : ZMod 21397) ^ 10698 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10698 : ZMod 21397)
      decide
    · change IsUnit ((2 : ZMod 21397) ^ 10698 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10698 : ZMod 21397)
      decide
    · change IsUnit ((2 : ZMod 21397) ^ 7132 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (21092 : ZMod 21397)
      decide
    · change IsUnit ((2 : ZMod 21397) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18821 : ZMod 21397)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21401 : Nat.Prime 21401 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21401 21400 1 3 [2, 2, 2, 5, 5, 107]
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
    · change IsUnit ((3 : ZMod 21401) ^ 10700 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10700 : ZMod 21401)
      decide
    · change IsUnit ((3 : ZMod 21401) ^ 10700 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10700 : ZMod 21401)
      decide
    · change IsUnit ((3 : ZMod 21401) ^ 10700 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10700 : ZMod 21401)
      decide
    · change IsUnit ((3 : ZMod 21401) ^ 4280 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19026 : ZMod 21401)
      decide
    · change IsUnit ((3 : ZMod 21401) ^ 4280 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19026 : ZMod 21401)
      decide
    · change IsUnit ((3 : ZMod 21401) ^ 200 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8897 : ZMod 21401)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21407 : Nat.Prime 21407 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21407 21406 1 5 [2, 7, 11, 139]
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
    · change IsUnit ((5 : ZMod 21407) ^ 10703 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10703 : ZMod 21407)
      decide
    · change IsUnit ((5 : ZMod 21407) ^ 3058 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (20311 : ZMod 21407)
      decide
    · change IsUnit ((5 : ZMod 21407) ^ 1946 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4887 : ZMod 21407)
      decide
    · change IsUnit ((5 : ZMod 21407) ^ 154 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (20612 : ZMod 21407)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21419 : Nat.Prime 21419 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21419 21418 1 2 [2, 10709]
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
    · change IsUnit ((2 : ZMod 21419) ^ 10709 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10709 : ZMod 21419)
      decide
    · change IsUnit ((2 : ZMod 21419) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7140 : ZMod 21419)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21347) (q := 21377) (by exact lowPrime_21377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21377) (q := 21379) (by exact lowPrime_21379) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21379) (q := 21383) (by exact lowPrime_21383) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21383) (q := 21391) (by exact lowPrime_21391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21391) (q := 21397) (by exact lowPrime_21397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21397) (q := 21401) (by exact lowPrime_21401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21401) (q := 21407) (by exact lowPrime_21407) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21407) (q := 21419) (by exact lowPrime_21419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part06_chain :
    DusartPrimeRowsChain 21347 21419 dusartPrimeRows_20959_22026_part06 := by
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
