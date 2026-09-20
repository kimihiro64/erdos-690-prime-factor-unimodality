import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 274 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_17393 : Nat.Prime 17393 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17393 17392 1 3 [2, 2, 2, 2, 1087]
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
    · change IsUnit ((3 : ZMod 17393) ^ 8696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8696 : ZMod 17393)
      decide
    · change IsUnit ((3 : ZMod 17393) ^ 8696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8696 : ZMod 17393)
      decide
    · change IsUnit ((3 : ZMod 17393) ^ 8696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8696 : ZMod 17393)
      decide
    · change IsUnit ((3 : ZMod 17393) ^ 8696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8696 : ZMod 17393)
      decide
    · change IsUnit ((3 : ZMod 17393) ^ 16 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3770 : ZMod 17393)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17401 : Nat.Prime 17401 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17401 17400 1 11 [2, 2, 2, 3, 5, 5, 29]
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
    · change IsUnit ((11 : ZMod 17401) ^ 8700 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8700 : ZMod 17401)
      decide
    · change IsUnit ((11 : ZMod 17401) ^ 8700 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8700 : ZMod 17401)
      decide
    · change IsUnit ((11 : ZMod 17401) ^ 8700 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8700 : ZMod 17401)
      decide
    · change IsUnit ((11 : ZMod 17401) ^ 5800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (201 : ZMod 17401)
      decide
    · change IsUnit ((11 : ZMod 17401) ^ 3480 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11290 : ZMod 17401)
      decide
    · change IsUnit ((11 : ZMod 17401) ^ 3480 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11290 : ZMod 17401)
      decide
    · change IsUnit ((11 : ZMod 17401) ^ 600 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4786 : ZMod 17401)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17417 : Nat.Prime 17417 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17417 17416 1 3 [2, 2, 2, 7, 311]
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
    · change IsUnit ((3 : ZMod 17417) ^ 8708 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8708 : ZMod 17417)
      decide
    · change IsUnit ((3 : ZMod 17417) ^ 8708 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8708 : ZMod 17417)
      decide
    · change IsUnit ((3 : ZMod 17417) ^ 8708 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8708 : ZMod 17417)
      decide
    · change IsUnit ((3 : ZMod 17417) ^ 2488 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14203 : ZMod 17417)
      decide
    · change IsUnit ((3 : ZMod 17417) ^ 56 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4925 : ZMod 17417)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17419 : Nat.Prime 17419 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17419 17418 1 3 [2, 3, 2903]
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
    · change IsUnit ((3 : ZMod 17419) ^ 8709 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8709 : ZMod 17419)
      decide
    · change IsUnit ((3 : ZMod 17419) ^ 5806 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13842 : ZMod 17419)
      decide
    · change IsUnit ((3 : ZMod 17419) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6245 : ZMod 17419)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17431 : Nat.Prime 17431 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17431 17430 1 3 [2, 3, 5, 7, 83]
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
    · change IsUnit ((3 : ZMod 17431) ^ 8715 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8715 : ZMod 17431)
      decide
    · change IsUnit ((3 : ZMod 17431) ^ 5810 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4815 : ZMod 17431)
      decide
    · change IsUnit ((3 : ZMod 17431) ^ 3486 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15936 : ZMod 17431)
      decide
    · change IsUnit ((3 : ZMod 17431) ^ 2490 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6648 : ZMod 17431)
      decide
    · change IsUnit ((3 : ZMod 17431) ^ 210 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1033 : ZMod 17431)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17443 : Nat.Prime 17443 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17443 17442 1 2 [2, 3, 3, 3, 17, 19]
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
    · change IsUnit ((2 : ZMod 17443) ^ 8721 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8721 : ZMod 17443)
      decide
    · change IsUnit ((2 : ZMod 17443) ^ 5814 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3773 : ZMod 17443)
      decide
    · change IsUnit ((2 : ZMod 17443) ^ 5814 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3773 : ZMod 17443)
      decide
    · change IsUnit ((2 : ZMod 17443) ^ 5814 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3773 : ZMod 17443)
      decide
    · change IsUnit ((2 : ZMod 17443) ^ 1026 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15897 : ZMod 17443)
      decide
    · change IsUnit ((2 : ZMod 17443) ^ 918 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5659 : ZMod 17443)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17449 : Nat.Prime 17449 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17449 17448 1 14 [2, 2, 2, 3, 727]
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
    · change IsUnit ((14 : ZMod 17449) ^ 8724 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8724 : ZMod 17449)
      decide
    · change IsUnit ((14 : ZMod 17449) ^ 8724 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8724 : ZMod 17449)
      decide
    · change IsUnit ((14 : ZMod 17449) ^ 8724 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8724 : ZMod 17449)
      decide
    · change IsUnit ((14 : ZMod 17449) ^ 5816 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11900 : ZMod 17449)
      decide
    · change IsUnit ((14 : ZMod 17449) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10142 : ZMod 17449)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17467 : Nat.Prime 17467 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17467 17466 1 3 [2, 3, 41, 71]
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
    · change IsUnit ((3 : ZMod 17467) ^ 8733 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8733 : ZMod 17467)
      decide
    · change IsUnit ((3 : ZMod 17467) ^ 5822 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9347 : ZMod 17467)
      decide
    · change IsUnit ((3 : ZMod 17467) ^ 426 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1064 : ZMod 17467)
      decide
    · change IsUnit ((3 : ZMod 17467) ^ 246 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1228 : ZMod 17467)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17389) (q := 17393) (by exact lowPrime_17393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17393) (q := 17401) (by exact lowPrime_17401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17401) (q := 17417) (by exact lowPrime_17417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17417) (q := 17419) (by exact lowPrime_17419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17419) (q := 17431) (by exact lowPrime_17431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17431) (q := 17443) (by exact lowPrime_17443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17443) (q := 17449) (by exact lowPrime_17449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17449) (q := 17467) (by exact lowPrime_17467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part04_chain :
    DusartPrimeRowsChain 17389 17467 dusartPrimeRows_17159_18040_part04 := by
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
