import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 276 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_17539 : Nat.Prime 17539 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17539 17538 1 3 [2, 3, 37, 79]
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
    · change IsUnit ((3 : ZMod 17539) ^ 8769 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8769 : ZMod 17539)
      decide
    · change IsUnit ((3 : ZMod 17539) ^ 5846 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11533 : ZMod 17539)
      decide
    · change IsUnit ((3 : ZMod 17539) ^ 474 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9401 : ZMod 17539)
      decide
    · change IsUnit ((3 : ZMod 17539) ^ 222 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12534 : ZMod 17539)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17551 : Nat.Prime 17551 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17551 17550 1 3 [2, 3, 3, 3, 5, 5, 13]
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
    · change IsUnit ((3 : ZMod 17551) ^ 8775 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8775 : ZMod 17551)
      decide
    · change IsUnit ((3 : ZMod 17551) ^ 5850 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7761 : ZMod 17551)
      decide
    · change IsUnit ((3 : ZMod 17551) ^ 5850 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7761 : ZMod 17551)
      decide
    · change IsUnit ((3 : ZMod 17551) ^ 5850 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7761 : ZMod 17551)
      decide
    · change IsUnit ((3 : ZMod 17551) ^ 3510 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15663 : ZMod 17551)
      decide
    · change IsUnit ((3 : ZMod 17551) ^ 3510 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15663 : ZMod 17551)
      decide
    · change IsUnit ((3 : ZMod 17551) ^ 1350 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14823 : ZMod 17551)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17569 : Nat.Prime 17569 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17569 17568 1 11 [2, 2, 2, 2, 2, 3, 3, 61]
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
    · change IsUnit ((11 : ZMod 17569) ^ 8784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8784 : ZMod 17569)
      decide
    · change IsUnit ((11 : ZMod 17569) ^ 8784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8784 : ZMod 17569)
      decide
    · change IsUnit ((11 : ZMod 17569) ^ 8784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8784 : ZMod 17569)
      decide
    · change IsUnit ((11 : ZMod 17569) ^ 8784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8784 : ZMod 17569)
      decide
    · change IsUnit ((11 : ZMod 17569) ^ 8784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8784 : ZMod 17569)
      decide
    · change IsUnit ((11 : ZMod 17569) ^ 5856 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7540 : ZMod 17569)
      decide
    · change IsUnit ((11 : ZMod 17569) ^ 5856 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7540 : ZMod 17569)
      decide
    · change IsUnit ((11 : ZMod 17569) ^ 288 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6249 : ZMod 17569)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17573 : Nat.Prime 17573 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17573 17572 1 2 [2, 2, 23, 191]
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
    · change IsUnit ((2 : ZMod 17573) ^ 8786 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8786 : ZMod 17573)
      decide
    · change IsUnit ((2 : ZMod 17573) ^ 8786 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8786 : ZMod 17573)
      decide
    · change IsUnit ((2 : ZMod 17573) ^ 764 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4240 : ZMod 17573)
      decide
    · change IsUnit ((2 : ZMod 17573) ^ 92 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16533 : ZMod 17573)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17579 : Nat.Prime 17579 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17579 17578 1 2 [2, 11, 17, 47]
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
    · change IsUnit ((2 : ZMod 17579) ^ 8789 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8789 : ZMod 17579)
      decide
    · change IsUnit ((2 : ZMod 17579) ^ 1598 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1505 : ZMod 17579)
      decide
    · change IsUnit ((2 : ZMod 17579) ^ 1034 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3061 : ZMod 17579)
      decide
    · change IsUnit ((2 : ZMod 17579) ^ 374 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1504 : ZMod 17579)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17581 : Nat.Prime 17581 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17581 17580 1 10 [2, 2, 3, 5, 293]
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
    · change IsUnit ((10 : ZMod 17581) ^ 8790 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8790 : ZMod 17581)
      decide
    · change IsUnit ((10 : ZMod 17581) ^ 8790 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8790 : ZMod 17581)
      decide
    · change IsUnit ((10 : ZMod 17581) ^ 5860 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15850 : ZMod 17581)
      decide
    · change IsUnit ((10 : ZMod 17581) ^ 3516 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4467 : ZMod 17581)
      decide
    · change IsUnit ((10 : ZMod 17581) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3624 : ZMod 17581)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17597 : Nat.Prime 17597 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17597 17596 1 2 [2, 2, 53, 83]
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
    · change IsUnit ((2 : ZMod 17597) ^ 8798 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8798 : ZMod 17597)
      decide
    · change IsUnit ((2 : ZMod 17597) ^ 8798 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8798 : ZMod 17597)
      decide
    · change IsUnit ((2 : ZMod 17597) ^ 332 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14545 : ZMod 17597)
      decide
    · change IsUnit ((2 : ZMod 17597) ^ 212 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7039 : ZMod 17597)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17599 : Nat.Prime 17599 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17599 17598 1 6 [2, 3, 7, 419]
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
    · change IsUnit ((6 : ZMod 17599) ^ 8799 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8799 : ZMod 17599)
      decide
    · change IsUnit ((6 : ZMod 17599) ^ 5866 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8128 : ZMod 17599)
      decide
    · change IsUnit ((6 : ZMod 17599) ^ 2514 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9114 : ZMod 17599)
      decide
    · change IsUnit ((6 : ZMod 17599) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7240 : ZMod 17599)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17519) (q := 17539) (by exact lowPrime_17539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17539) (q := 17551) (by exact lowPrime_17551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17551) (q := 17569) (by exact lowPrime_17569) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17569) (q := 17573) (by exact lowPrime_17573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17573) (q := 17579) (by exact lowPrime_17579) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17579) (q := 17581) (by exact lowPrime_17581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17581) (q := 17597) (by exact lowPrime_17597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17597) (q := 17599) (by exact lowPrime_17599) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part06_chain :
    DusartPrimeRowsChain 17519 17599 dusartPrimeRows_17159_18040_part06 := by
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
