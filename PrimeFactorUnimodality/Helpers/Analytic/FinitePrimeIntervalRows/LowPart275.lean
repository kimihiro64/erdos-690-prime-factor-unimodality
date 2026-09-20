import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 275 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_17471 : Nat.Prime 17471 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17471 17470 1 11 [2, 5, 1747]
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
    · change IsUnit ((11 : ZMod 17471) ^ 8735 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8735 : ZMod 17471)
      decide
    · change IsUnit ((11 : ZMod 17471) ^ 3494 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7310 : ZMod 17471)
      decide
    · change IsUnit ((11 : ZMod 17471) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16225 : ZMod 17471)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17477 : Nat.Prime 17477 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17477 17476 1 2 [2, 2, 17, 257]
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
    · change IsUnit ((2 : ZMod 17477) ^ 8738 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8738 : ZMod 17477)
      decide
    · change IsUnit ((2 : ZMod 17477) ^ 8738 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8738 : ZMod 17477)
      decide
    · change IsUnit ((2 : ZMod 17477) ^ 1028 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8004 : ZMod 17477)
      decide
    · change IsUnit ((2 : ZMod 17477) ^ 68 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8236 : ZMod 17477)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17483 : Nat.Prime 17483 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17483 17482 1 2 [2, 8741]
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
    · change IsUnit ((2 : ZMod 17483) ^ 8741 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8741 : ZMod 17483)
      decide
    · change IsUnit ((2 : ZMod 17483) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5828 : ZMod 17483)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17489 : Nat.Prime 17489 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17489 17488 1 3 [2, 2, 2, 2, 1093]
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
    · change IsUnit ((3 : ZMod 17489) ^ 8744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8744 : ZMod 17489)
      decide
    · change IsUnit ((3 : ZMod 17489) ^ 8744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8744 : ZMod 17489)
      decide
    · change IsUnit ((3 : ZMod 17489) ^ 8744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8744 : ZMod 17489)
      decide
    · change IsUnit ((3 : ZMod 17489) ^ 8744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8744 : ZMod 17489)
      decide
    · change IsUnit ((3 : ZMod 17489) ^ 16 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17350 : ZMod 17489)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17491 : Nat.Prime 17491 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17491 17490 1 3 [2, 3, 5, 11, 53]
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
    · change IsUnit ((3 : ZMod 17491) ^ 8745 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8745 : ZMod 17491)
      decide
    · change IsUnit ((3 : ZMod 17491) ^ 5830 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5267 : ZMod 17491)
      decide
    · change IsUnit ((3 : ZMod 17491) ^ 3498 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10184 : ZMod 17491)
      decide
    · change IsUnit ((3 : ZMod 17491) ^ 1590 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10644 : ZMod 17491)
      decide
    · change IsUnit ((3 : ZMod 17491) ^ 330 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10972 : ZMod 17491)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17497 : Nat.Prime 17497 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17497 17496 1 5 [2, 2, 2, 3, 3, 3, 3, 3, 3, 3]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((5 : ZMod 17497) ^ 8748 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8748 : ZMod 17497)
      decide
    · change IsUnit ((5 : ZMod 17497) ^ 8748 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8748 : ZMod 17497)
      decide
    · change IsUnit ((5 : ZMod 17497) ^ 8748 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8748 : ZMod 17497)
      decide
    · change IsUnit ((5 : ZMod 17497) ^ 5832 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10091 : ZMod 17497)
      decide
    · change IsUnit ((5 : ZMod 17497) ^ 5832 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10091 : ZMod 17497)
      decide
    · change IsUnit ((5 : ZMod 17497) ^ 5832 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10091 : ZMod 17497)
      decide
    · change IsUnit ((5 : ZMod 17497) ^ 5832 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10091 : ZMod 17497)
      decide
    · change IsUnit ((5 : ZMod 17497) ^ 5832 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10091 : ZMod 17497)
      decide
    · change IsUnit ((5 : ZMod 17497) ^ 5832 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10091 : ZMod 17497)
      decide
    · change IsUnit ((5 : ZMod 17497) ^ 5832 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10091 : ZMod 17497)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17509 : Nat.Prime 17509 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17509 17508 1 2 [2, 2, 3, 1459]
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
    · change IsUnit ((2 : ZMod 17509) ^ 8754 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8754 : ZMod 17509)
      decide
    · change IsUnit ((2 : ZMod 17509) ^ 8754 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8754 : ZMod 17509)
      decide
    · change IsUnit ((2 : ZMod 17509) ^ 5836 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4460 : ZMod 17509)
      decide
    · change IsUnit ((2 : ZMod 17509) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16594 : ZMod 17509)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17519 : Nat.Prime 17519 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17519 17518 1 13 [2, 19, 461]
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
    · change IsUnit ((13 : ZMod 17519) ^ 8759 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8759 : ZMod 17519)
      decide
    · change IsUnit ((13 : ZMod 17519) ^ 922 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16464 : ZMod 17519)
      decide
    · change IsUnit ((13 : ZMod 17519) ^ 38 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13983 : ZMod 17519)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17467) (q := 17471) (by exact lowPrime_17471) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17471) (q := 17477) (by exact lowPrime_17477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17477) (q := 17483) (by exact lowPrime_17483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17483) (q := 17489) (by exact lowPrime_17489) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17489) (q := 17491) (by exact lowPrime_17491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17491) (q := 17497) (by exact lowPrime_17497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17497) (q := 17509) (by exact lowPrime_17509) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17509) (q := 17519) (by exact lowPrime_17519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part05_chain :
    DusartPrimeRowsChain 17467 17519 dusartPrimeRows_17159_18040_part05 := by
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
