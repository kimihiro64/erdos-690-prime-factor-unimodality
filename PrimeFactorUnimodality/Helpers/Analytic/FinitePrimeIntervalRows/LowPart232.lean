import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 232 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_21977 : Nat.Prime 21977 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21977 21976 1 3 [2, 2, 2, 41, 67]
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
    · change IsUnit ((3 : ZMod 21977) ^ 10988 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10988 : ZMod 21977)
      decide
    · change IsUnit ((3 : ZMod 21977) ^ 10988 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10988 : ZMod 21977)
      decide
    · change IsUnit ((3 : ZMod 21977) ^ 10988 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10988 : ZMod 21977)
      decide
    · change IsUnit ((3 : ZMod 21977) ^ 536 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7023 : ZMod 21977)
      decide
    · change IsUnit ((3 : ZMod 21977) ^ 328 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12528 : ZMod 21977)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21991 : Nat.Prime 21991 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21991 21990 1 3 [2, 3, 5, 733]
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
    · change IsUnit ((3 : ZMod 21991) ^ 10995 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10995 : ZMod 21991)
      decide
    · change IsUnit ((3 : ZMod 21991) ^ 7330 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10016 : ZMod 21991)
      decide
    · change IsUnit ((3 : ZMod 21991) ^ 4398 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2477 : ZMod 21991)
      decide
    · change IsUnit ((3 : ZMod 21991) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11053 : ZMod 21991)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21997 : Nat.Prime 21997 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21997 21996 1 7 [2, 2, 3, 3, 13, 47]
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
    · change IsUnit ((7 : ZMod 21997) ^ 10998 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10998 : ZMod 21997)
      decide
    · change IsUnit ((7 : ZMod 21997) ^ 10998 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10998 : ZMod 21997)
      decide
    · change IsUnit ((7 : ZMod 21997) ^ 7332 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18128 : ZMod 21997)
      decide
    · change IsUnit ((7 : ZMod 21997) ^ 7332 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18128 : ZMod 21997)
      decide
    · change IsUnit ((7 : ZMod 21997) ^ 1692 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1430 : ZMod 21997)
      decide
    · change IsUnit ((7 : ZMod 21997) ^ 468 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8780 : ZMod 21997)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22003 : Nat.Prime 22003 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22003 22002 1 2 [2, 3, 19, 193]
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
    · change IsUnit ((2 : ZMod 22003) ^ 11001 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11001 : ZMod 22003)
      decide
    · change IsUnit ((2 : ZMod 22003) ^ 7334 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15526 : ZMod 22003)
      decide
    · change IsUnit ((2 : ZMod 22003) ^ 1158 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (290 : ZMod 22003)
      decide
    · change IsUnit ((2 : ZMod 22003) ^ 114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18761 : ZMod 22003)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22013 : Nat.Prime 22013 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22013 22012 1 2 [2, 2, 5503]
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
    · change IsUnit ((2 : ZMod 22013) ^ 11006 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11006 : ZMod 22013)
      decide
    · change IsUnit ((2 : ZMod 22013) ^ 11006 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11006 : ZMod 22013)
      decide
    · change IsUnit ((2 : ZMod 22013) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19078 : ZMod 22013)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22027 : Nat.Prime 22027 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22027 22026 1 3 [2, 3, 3671]
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
    · change IsUnit ((3 : ZMod 22027) ^ 11013 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11013 : ZMod 22027)
      decide
    · change IsUnit ((3 : ZMod 22027) ^ 7342 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8885 : ZMod 22027)
      decide
    · change IsUnit ((3 : ZMod 22027) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3298 : ZMod 22027)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part14 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21961) (q := 21977) (by exact lowPrime_21977) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21977) (q := 21991) (by exact lowPrime_21991) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21991) (q := 21997) (by exact lowPrime_21997) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21997) (q := 22003) (by exact lowPrime_22003) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 22003) (q := 22013) (by exact lowPrime_22013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 22013) (q := 22027) (by exact lowPrime_22027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part14_chain :
    DusartPrimeRowsChain 21961 22027 dusartPrimeRows_20959_22026_part14 := by
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
            · apply DusartPrimeRowsChain.empty
              norm_num
