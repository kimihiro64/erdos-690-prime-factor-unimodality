import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 125 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_11491 : Nat.Prime 11491 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11491 11490 1 3 [2, 3, 5, 383]
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
    · change IsUnit ((3 : ZMod 11491) ^ 5745 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5745 : ZMod 11491)
      decide
    · change IsUnit ((3 : ZMod 11491) ^ 3830 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3701 : ZMod 11491)
      decide
    · change IsUnit ((3 : ZMod 11491) ^ 2298 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3078 : ZMod 11491)
      decide
    · change IsUnit ((3 : ZMod 11491) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6464 : ZMod 11491)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11497 : Nat.Prime 11497 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11497 11496 1 7 [2, 2, 2, 3, 479]
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
    · change IsUnit ((7 : ZMod 11497) ^ 5748 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5748 : ZMod 11497)
      decide
    · change IsUnit ((7 : ZMod 11497) ^ 5748 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5748 : ZMod 11497)
      decide
    · change IsUnit ((7 : ZMod 11497) ^ 5748 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5748 : ZMod 11497)
      decide
    · change IsUnit ((7 : ZMod 11497) ^ 3832 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (483 : ZMod 11497)
      decide
    · change IsUnit ((7 : ZMod 11497) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7895 : ZMod 11497)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11503 : Nat.Prime 11503 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11503 11502 1 3 [2, 3, 3, 3, 3, 71]
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
    · change IsUnit ((3 : ZMod 11503) ^ 5751 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5751 : ZMod 11503)
      decide
    · change IsUnit ((3 : ZMod 11503) ^ 3834 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3678 : ZMod 11503)
      decide
    · change IsUnit ((3 : ZMod 11503) ^ 3834 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3678 : ZMod 11503)
      decide
    · change IsUnit ((3 : ZMod 11503) ^ 3834 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3678 : ZMod 11503)
      decide
    · change IsUnit ((3 : ZMod 11503) ^ 3834 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3678 : ZMod 11503)
      decide
    · change IsUnit ((3 : ZMod 11503) ^ 162 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6309 : ZMod 11503)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11489) (q := 11491) (by exact lowPrime_11491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11491) (q := 11497) (by exact lowPrime_11497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11497) (q := 11503) (by exact lowPrime_11503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part08_chain :
    DusartPrimeRowsChain 11489 11503 dusartPrimeRows_10939_11502_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.empty
        norm_num
