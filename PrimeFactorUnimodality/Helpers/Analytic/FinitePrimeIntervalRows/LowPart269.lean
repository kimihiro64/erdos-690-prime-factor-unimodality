import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 269 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_18839 : Nat.Prime 18839 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18839 18838 1 7 [2, 9419]
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
    · change IsUnit ((7 : ZMod 18839) ^ 9419 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9419 : ZMod 18839)
      decide
    · change IsUnit ((7 : ZMod 18839) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9812 : ZMod 18839)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18859 : Nat.Prime 18859 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18859 18858 1 2 [2, 3, 7, 449]
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
    · change IsUnit ((2 : ZMod 18859) ^ 9429 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9429 : ZMod 18859)
      decide
    · change IsUnit ((2 : ZMod 18859) ^ 6286 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7141 : ZMod 18859)
      decide
    · change IsUnit ((2 : ZMod 18859) ^ 2694 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14750 : ZMod 18859)
      decide
    · change IsUnit ((2 : ZMod 18859) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4694 : ZMod 18859)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18869 : Nat.Prime 18869 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18869 18868 1 2 [2, 2, 53, 89]
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
    · change IsUnit ((2 : ZMod 18869) ^ 9434 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9434 : ZMod 18869)
      decide
    · change IsUnit ((2 : ZMod 18869) ^ 9434 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9434 : ZMod 18869)
      decide
    · change IsUnit ((2 : ZMod 18869) ^ 356 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12409 : ZMod 18869)
      decide
    · change IsUnit ((2 : ZMod 18869) ^ 212 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17623 : ZMod 18869)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18899 : Nat.Prime 18899 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18899 18898 1 2 [2, 11, 859]
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
    · change IsUnit ((2 : ZMod 18899) ^ 9449 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9449 : ZMod 18899)
      decide
    · change IsUnit ((2 : ZMod 18899) ^ 1718 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16746 : ZMod 18899)
      decide
    · change IsUnit ((2 : ZMod 18899) ^ 22 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4432 : ZMod 18899)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18911 : Nat.Prime 18911 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18911 18910 1 14 [2, 5, 31, 61]
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
    · change IsUnit ((14 : ZMod 18911) ^ 9455 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9455 : ZMod 18911)
      decide
    · change IsUnit ((14 : ZMod 18911) ^ 3782 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4322 : ZMod 18911)
      decide
    · change IsUnit ((14 : ZMod 18911) ^ 610 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14786 : ZMod 18911)
      decide
    · change IsUnit ((14 : ZMod 18911) ^ 310 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17232 : ZMod 18911)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18913 : Nat.Prime 18913 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18913 18912 1 7 [2, 2, 2, 2, 2, 3, 197]
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
    · change IsUnit ((7 : ZMod 18913) ^ 9456 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9456 : ZMod 18913)
      decide
    · change IsUnit ((7 : ZMod 18913) ^ 9456 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9456 : ZMod 18913)
      decide
    · change IsUnit ((7 : ZMod 18913) ^ 9456 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9456 : ZMod 18913)
      decide
    · change IsUnit ((7 : ZMod 18913) ^ 9456 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9456 : ZMod 18913)
      decide
    · change IsUnit ((7 : ZMod 18913) ^ 9456 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9456 : ZMod 18913)
      decide
    · change IsUnit ((7 : ZMod 18913) ^ 6304 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10522 : ZMod 18913)
      decide
    · change IsUnit ((7 : ZMod 18913) ^ 96 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5798 : ZMod 18913)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18917 : Nat.Prime 18917 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18917 18916 1 2 [2, 2, 4729]
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
    · change IsUnit ((2 : ZMod 18917) ^ 9458 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9458 : ZMod 18917)
      decide
    · change IsUnit ((2 : ZMod 18917) ^ 9458 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9458 : ZMod 18917)
      decide
    · change IsUnit ((2 : ZMod 18917) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8828 : ZMod 18917)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18919 : Nat.Prime 18919 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18919 18918 1 3 [2, 3, 3, 1051]
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
    · change IsUnit ((3 : ZMod 18919) ^ 9459 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9459 : ZMod 18919)
      decide
    · change IsUnit ((3 : ZMod 18919) ^ 6306 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18240 : ZMod 18919)
      decide
    · change IsUnit ((3 : ZMod 18919) ^ 6306 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18240 : ZMod 18919)
      decide
    · change IsUnit ((3 : ZMod 18919) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5803 : ZMod 18919)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18803) (q := 18839) (by exact lowPrime_18839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18839) (q := 18859) (by exact lowPrime_18859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18859) (q := 18869) (by exact lowPrime_18869) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18869) (q := 18899) (by exact lowPrime_18899) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18899) (q := 18911) (by exact lowPrime_18911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18911) (q := 18913) (by exact lowPrime_18913) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18913) (q := 18917) (by exact lowPrime_18917) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18917) (q := 18919) (by exact lowPrime_18919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part11_chain :
    DusartPrimeRowsChain 18803 18919 dusartPrimeRows_18041_18958_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num
