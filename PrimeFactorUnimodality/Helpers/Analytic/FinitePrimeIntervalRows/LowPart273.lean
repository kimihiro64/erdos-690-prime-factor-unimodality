import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 273 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_17333 : Nat.Prime 17333 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17333 17332 1 2 [2, 2, 7, 619]
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
    · change IsUnit ((2 : ZMod 17333) ^ 8666 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8666 : ZMod 17333)
      decide
    · change IsUnit ((2 : ZMod 17333) ^ 8666 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8666 : ZMod 17333)
      decide
    · change IsUnit ((2 : ZMod 17333) ^ 2476 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (457 : ZMod 17333)
      decide
    · change IsUnit ((2 : ZMod 17333) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4188 : ZMod 17333)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17341 : Nat.Prime 17341 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17341 17340 1 6 [2, 2, 3, 5, 17, 17]
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
    · change IsUnit ((6 : ZMod 17341) ^ 8670 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8670 : ZMod 17341)
      decide
    · change IsUnit ((6 : ZMod 17341) ^ 8670 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8670 : ZMod 17341)
      decide
    · change IsUnit ((6 : ZMod 17341) ^ 5780 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14546 : ZMod 17341)
      decide
    · change IsUnit ((6 : ZMod 17341) ^ 3468 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11695 : ZMod 17341)
      decide
    · change IsUnit ((6 : ZMod 17341) ^ 1020 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7077 : ZMod 17341)
      decide
    · change IsUnit ((6 : ZMod 17341) ^ 1020 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7077 : ZMod 17341)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17351 : Nat.Prime 17351 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17351 17350 1 11 [2, 5, 5, 347]
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
    · change IsUnit ((11 : ZMod 17351) ^ 8675 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8675 : ZMod 17351)
      decide
    · change IsUnit ((11 : ZMod 17351) ^ 3470 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6361 : ZMod 17351)
      decide
    · change IsUnit ((11 : ZMod 17351) ^ 3470 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6361 : ZMod 17351)
      decide
    · change IsUnit ((11 : ZMod 17351) ^ 50 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14773 : ZMod 17351)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17359 : Nat.Prime 17359 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17359 17358 1 3 [2, 3, 11, 263]
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
    · change IsUnit ((3 : ZMod 17359) ^ 8679 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8679 : ZMod 17359)
      decide
    · change IsUnit ((3 : ZMod 17359) ^ 5786 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5130 : ZMod 17359)
      decide
    · change IsUnit ((3 : ZMod 17359) ^ 1578 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14631 : ZMod 17359)
      decide
    · change IsUnit ((3 : ZMod 17359) ^ 66 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12255 : ZMod 17359)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17377 : Nat.Prime 17377 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17377 17376 1 7 [2, 2, 2, 2, 2, 3, 181]
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
    · change IsUnit ((7 : ZMod 17377) ^ 8688 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8688 : ZMod 17377)
      decide
    · change IsUnit ((7 : ZMod 17377) ^ 8688 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8688 : ZMod 17377)
      decide
    · change IsUnit ((7 : ZMod 17377) ^ 8688 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8688 : ZMod 17377)
      decide
    · change IsUnit ((7 : ZMod 17377) ^ 8688 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8688 : ZMod 17377)
      decide
    · change IsUnit ((7 : ZMod 17377) ^ 8688 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8688 : ZMod 17377)
      decide
    · change IsUnit ((7 : ZMod 17377) ^ 5792 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11165 : ZMod 17377)
      decide
    · change IsUnit ((7 : ZMod 17377) ^ 96 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4457 : ZMod 17377)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17383 : Nat.Prime 17383 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17383 17382 1 5 [2, 3, 2897]
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
    · change IsUnit ((5 : ZMod 17383) ^ 8691 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8691 : ZMod 17383)
      decide
    · change IsUnit ((5 : ZMod 17383) ^ 5794 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1057 : ZMod 17383)
      decide
    · change IsUnit ((5 : ZMod 17383) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17215 : ZMod 17383)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17387 : Nat.Prime 17387 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17387 17386 1 2 [2, 8693]
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
    · change IsUnit ((2 : ZMod 17387) ^ 8693 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8693 : ZMod 17387)
      decide
    · change IsUnit ((2 : ZMod 17387) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5796 : ZMod 17387)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17389 : Nat.Prime 17389 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17389 17388 1 2 [2, 2, 3, 3, 3, 7, 23]
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
    · change IsUnit ((2 : ZMod 17389) ^ 8694 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8694 : ZMod 17389)
      decide
    · change IsUnit ((2 : ZMod 17389) ^ 8694 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8694 : ZMod 17389)
      decide
    · change IsUnit ((2 : ZMod 17389) ^ 5796 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10378 : ZMod 17389)
      decide
    · change IsUnit ((2 : ZMod 17389) ^ 5796 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10378 : ZMod 17389)
      decide
    · change IsUnit ((2 : ZMod 17389) ^ 5796 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10378 : ZMod 17389)
      decide
    · change IsUnit ((2 : ZMod 17389) ^ 2484 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1874 : ZMod 17389)
      decide
    · change IsUnit ((2 : ZMod 17389) ^ 756 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17385 : ZMod 17389)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17327) (q := 17333) (by exact lowPrime_17333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17333) (q := 17341) (by exact lowPrime_17341) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17341) (q := 17351) (by exact lowPrime_17351) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17351) (q := 17359) (by exact lowPrime_17359) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17359) (q := 17377) (by exact lowPrime_17377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17377) (q := 17383) (by exact lowPrime_17383) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17383) (q := 17387) (by exact lowPrime_17387) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17387) (q := 17389) (by exact lowPrime_17389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part03_chain :
    DusartPrimeRowsChain 17327 17389 dusartPrimeRows_17159_18040_part03 := by
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
