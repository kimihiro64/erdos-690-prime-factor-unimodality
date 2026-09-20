import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 277 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_17609 : Nat.Prime 17609 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17609 17608 1 3 [2, 2, 2, 31, 71]
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
    · change IsUnit ((3 : ZMod 17609) ^ 8804 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8804 : ZMod 17609)
      decide
    · change IsUnit ((3 : ZMod 17609) ^ 8804 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8804 : ZMod 17609)
      decide
    · change IsUnit ((3 : ZMod 17609) ^ 8804 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8804 : ZMod 17609)
      decide
    · change IsUnit ((3 : ZMod 17609) ^ 568 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11613 : ZMod 17609)
      decide
    · change IsUnit ((3 : ZMod 17609) ^ 248 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10622 : ZMod 17609)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17623 : Nat.Prime 17623 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17623 17622 1 3 [2, 3, 3, 11, 89]
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
    · change IsUnit ((3 : ZMod 17623) ^ 8811 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8811 : ZMod 17623)
      decide
    · change IsUnit ((3 : ZMod 17623) ^ 5874 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4757 : ZMod 17623)
      decide
    · change IsUnit ((3 : ZMod 17623) ^ 5874 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4757 : ZMod 17623)
      decide
    · change IsUnit ((3 : ZMod 17623) ^ 1602 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17293 : ZMod 17623)
      decide
    · change IsUnit ((3 : ZMod 17623) ^ 198 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12378 : ZMod 17623)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17627 : Nat.Prime 17627 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17627 17626 1 2 [2, 7, 1259]
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
    · change IsUnit ((2 : ZMod 17627) ^ 8813 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8813 : ZMod 17627)
      decide
    · change IsUnit ((2 : ZMod 17627) ^ 2518 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14848 : ZMod 17627)
      decide
    · change IsUnit ((2 : ZMod 17627) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4010 : ZMod 17627)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17657 : Nat.Prime 17657 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17657 17656 1 3 [2, 2, 2, 2207]
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
    · change IsUnit ((3 : ZMod 17657) ^ 8828 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8828 : ZMod 17657)
      decide
    · change IsUnit ((3 : ZMod 17657) ^ 8828 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8828 : ZMod 17657)
      decide
    · change IsUnit ((3 : ZMod 17657) ^ 8828 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8828 : ZMod 17657)
      decide
    · change IsUnit ((3 : ZMod 17657) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9278 : ZMod 17657)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17659 : Nat.Prime 17659 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17659 17658 1 3 [2, 3, 3, 3, 3, 109]
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
    · change IsUnit ((3 : ZMod 17659) ^ 8829 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8829 : ZMod 17659)
      decide
    · change IsUnit ((3 : ZMod 17659) ^ 5886 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8515 : ZMod 17659)
      decide
    · change IsUnit ((3 : ZMod 17659) ^ 5886 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8515 : ZMod 17659)
      decide
    · change IsUnit ((3 : ZMod 17659) ^ 5886 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8515 : ZMod 17659)
      decide
    · change IsUnit ((3 : ZMod 17659) ^ 5886 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8515 : ZMod 17659)
      decide
    · change IsUnit ((3 : ZMod 17659) ^ 162 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15537 : ZMod 17659)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17669 : Nat.Prime 17669 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17669 17668 1 2 [2, 2, 7, 631]
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
    · change IsUnit ((2 : ZMod 17669) ^ 8834 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8834 : ZMod 17669)
      decide
    · change IsUnit ((2 : ZMod 17669) ^ 8834 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8834 : ZMod 17669)
      decide
    · change IsUnit ((2 : ZMod 17669) ^ 2524 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2582 : ZMod 17669)
      decide
    · change IsUnit ((2 : ZMod 17669) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13911 : ZMod 17669)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17681 : Nat.Prime 17681 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17681 17680 1 3 [2, 2, 2, 2, 5, 13, 17]
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
    · change IsUnit ((3 : ZMod 17681) ^ 8840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8840 : ZMod 17681)
      decide
    · change IsUnit ((3 : ZMod 17681) ^ 8840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8840 : ZMod 17681)
      decide
    · change IsUnit ((3 : ZMod 17681) ^ 8840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8840 : ZMod 17681)
      decide
    · change IsUnit ((3 : ZMod 17681) ^ 8840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8840 : ZMod 17681)
      decide
    · change IsUnit ((3 : ZMod 17681) ^ 3536 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2155 : ZMod 17681)
      decide
    · change IsUnit ((3 : ZMod 17681) ^ 1360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15632 : ZMod 17681)
      decide
    · change IsUnit ((3 : ZMod 17681) ^ 1040 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6294 : ZMod 17681)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17683 : Nat.Prime 17683 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17683 17682 1 5 [2, 3, 7, 421]
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
    · change IsUnit ((5 : ZMod 17683) ^ 8841 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8841 : ZMod 17683)
      decide
    · change IsUnit ((5 : ZMod 17683) ^ 5894 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13145 : ZMod 17683)
      decide
    · change IsUnit ((5 : ZMod 17683) ^ 2526 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6362 : ZMod 17683)
      decide
    · change IsUnit ((5 : ZMod 17683) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10940 : ZMod 17683)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17599) (q := 17609) (by exact lowPrime_17609) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17609) (q := 17623) (by exact lowPrime_17623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17623) (q := 17627) (by exact lowPrime_17627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17627) (q := 17657) (by exact lowPrime_17657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17657) (q := 17659) (by exact lowPrime_17659) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17659) (q := 17669) (by exact lowPrime_17669) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17669) (q := 17681) (by exact lowPrime_17681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17681) (q := 17683) (by exact lowPrime_17683) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part07_chain :
    DusartPrimeRowsChain 17599 17683 dusartPrimeRows_17159_18040_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num
