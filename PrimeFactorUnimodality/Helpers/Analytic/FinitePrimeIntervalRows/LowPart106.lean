import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 106 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_10091 : Nat.Prime 10091 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10091 10090 1 2 [2, 5, 1009]
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
    · change IsUnit ((2 : ZMod 10091) ^ 5045 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5045 : ZMod 10091)
      decide
    · change IsUnit ((2 : ZMod 10091) ^ 2018 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5246 : ZMod 10091)
      decide
    · change IsUnit ((2 : ZMod 10091) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1815 : ZMod 10091)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10093 : Nat.Prime 10093 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10093 10092 1 2 [2, 2, 3, 29, 29]
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
    · change IsUnit ((2 : ZMod 10093) ^ 5046 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5046 : ZMod 10093)
      decide
    · change IsUnit ((2 : ZMod 10093) ^ 5046 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5046 : ZMod 10093)
      decide
    · change IsUnit ((2 : ZMod 10093) ^ 3364 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5017 : ZMod 10093)
      decide
    · change IsUnit ((2 : ZMod 10093) ^ 348 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4299 : ZMod 10093)
      decide
    · change IsUnit ((2 : ZMod 10093) ^ 348 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4299 : ZMod 10093)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10099 : Nat.Prime 10099 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10099 10098 1 2 [2, 3, 3, 3, 11, 17]
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
    · change IsUnit ((2 : ZMod 10099) ^ 5049 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5049 : ZMod 10099)
      decide
    · change IsUnit ((2 : ZMod 10099) ^ 3366 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8048 : ZMod 10099)
      decide
    · change IsUnit ((2 : ZMod 10099) ^ 3366 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8048 : ZMod 10099)
      decide
    · change IsUnit ((2 : ZMod 10099) ^ 3366 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8048 : ZMod 10099)
      decide
    · change IsUnit ((2 : ZMod 10099) ^ 918 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5324 : ZMod 10099)
      decide
    · change IsUnit ((2 : ZMod 10099) ^ 594 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1770 : ZMod 10099)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10103 : Nat.Prime 10103 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10103 10102 1 5 [2, 5051]
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
    · change IsUnit ((5 : ZMod 10103) ^ 5051 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5051 : ZMod 10103)
      decide
    · change IsUnit ((5 : ZMod 10103) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (421 : ZMod 10103)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10111 : Nat.Prime 10111 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10111 10110 1 12 [2, 3, 5, 337]
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
    · change IsUnit ((12 : ZMod 10111) ^ 5055 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5055 : ZMod 10111)
      decide
    · change IsUnit ((12 : ZMod 10111) ^ 3370 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5313 : ZMod 10111)
      decide
    · change IsUnit ((12 : ZMod 10111) ^ 2022 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8110 : ZMod 10111)
      decide
    · change IsUnit ((12 : ZMod 10111) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2614 : ZMod 10111)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10133 : Nat.Prime 10133 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10133 10132 1 2 [2, 2, 17, 149]
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
    · change IsUnit ((2 : ZMod 10133) ^ 5066 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5066 : ZMod 10133)
      decide
    · change IsUnit ((2 : ZMod 10133) ^ 5066 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5066 : ZMod 10133)
      decide
    · change IsUnit ((2 : ZMod 10133) ^ 596 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9859 : ZMod 10133)
      decide
    · change IsUnit ((2 : ZMod 10133) ^ 68 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6347 : ZMod 10133)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10139 : Nat.Prime 10139 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10139 10138 1 2 [2, 37, 137]
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
    · change IsUnit ((2 : ZMod 10139) ^ 5069 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5069 : ZMod 10139)
      decide
    · change IsUnit ((2 : ZMod 10139) ^ 274 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9987 : ZMod 10139)
      decide
    · change IsUnit ((2 : ZMod 10139) ^ 74 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5073 : ZMod 10139)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10141 : Nat.Prime 10141 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10141 10140 1 2 [2, 2, 3, 5, 13, 13]
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
    · change IsUnit ((2 : ZMod 10141) ^ 5070 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5070 : ZMod 10141)
      decide
    · change IsUnit ((2 : ZMod 10141) ^ 5070 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5070 : ZMod 10141)
      decide
    · change IsUnit ((2 : ZMod 10141) ^ 3380 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9412 : ZMod 10141)
      decide
    · change IsUnit ((2 : ZMod 10141) ^ 2028 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7257 : ZMod 10141)
      decide
    · change IsUnit ((2 : ZMod 10141) ^ 780 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5274 : ZMod 10141)
      decide
    · change IsUnit ((2 : ZMod 10141) ^ 780 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5274 : ZMod 10141)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10079) (q := 10091) (by exact lowPrime_10091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10091) (q := 10093) (by exact lowPrime_10093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10093) (q := 10099) (by exact lowPrime_10099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10099) (q := 10103) (by exact lowPrime_10103) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10103) (q := 10111) (by exact lowPrime_10111) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10111) (q := 10133) (by exact lowPrime_10133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10133) (q := 10139) (by exact lowPrime_10139) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10139) (q := 10141) (by exact lowPrime_10141) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part03_chain :
    DusartPrimeRowsChain 10079 10141 dusartPrimeRows_9901_10426_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num
