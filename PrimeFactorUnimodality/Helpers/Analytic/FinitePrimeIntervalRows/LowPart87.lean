import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 87 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_8783 : Nat.Prime 8783 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8783 8782 1 5 [2, 4391]
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
    · change IsUnit ((5 : ZMod 8783) ^ 4391 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4391 : ZMod 8783)
      decide
    · change IsUnit ((5 : ZMod 8783) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (366 : ZMod 8783)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8803 : Nat.Prime 8803 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8803 8802 1 2 [2, 3, 3, 3, 163]
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
    · change IsUnit ((2 : ZMod 8803) ^ 4401 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4401 : ZMod 8803)
      decide
    · change IsUnit ((2 : ZMod 8803) ^ 2934 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (329 : ZMod 8803)
      decide
    · change IsUnit ((2 : ZMod 8803) ^ 2934 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (329 : ZMod 8803)
      decide
    · change IsUnit ((2 : ZMod 8803) ^ 2934 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (329 : ZMod 8803)
      decide
    · change IsUnit ((2 : ZMod 8803) ^ 54 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4013 : ZMod 8803)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8807 : Nat.Prime 8807 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8807 8806 1 5 [2, 7, 17, 37]
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
    · change IsUnit ((5 : ZMod 8807) ^ 4403 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4403 : ZMod 8807)
      decide
    · change IsUnit ((5 : ZMod 8807) ^ 1258 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2565 : ZMod 8807)
      decide
    · change IsUnit ((5 : ZMod 8807) ^ 518 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1137 : ZMod 8807)
      decide
    · change IsUnit ((5 : ZMod 8807) ^ 238 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8605 : ZMod 8807)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8819 : Nat.Prime 8819 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8819 8818 1 2 [2, 4409]
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
    · change IsUnit ((2 : ZMod 8819) ^ 4409 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4409 : ZMod 8819)
      decide
    · change IsUnit ((2 : ZMod 8819) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2940 : ZMod 8819)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8821 : Nat.Prime 8821 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8821 8820 1 2 [2, 2, 3, 3, 5, 7, 7]
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
    · change IsUnit ((2 : ZMod 8821) ^ 4410 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4410 : ZMod 8821)
      decide
    · change IsUnit ((2 : ZMod 8821) ^ 4410 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4410 : ZMod 8821)
      decide
    · change IsUnit ((2 : ZMod 8821) ^ 2940 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3752 : ZMod 8821)
      decide
    · change IsUnit ((2 : ZMod 8821) ^ 2940 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3752 : ZMod 8821)
      decide
    · change IsUnit ((2 : ZMod 8821) ^ 1764 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5349 : ZMod 8821)
      decide
    · change IsUnit ((2 : ZMod 8821) ^ 1260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8403 : ZMod 8821)
      decide
    · change IsUnit ((2 : ZMod 8821) ^ 1260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8403 : ZMod 8821)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8831 : Nat.Prime 8831 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8831 8830 1 7 [2, 5, 883]
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
    · change IsUnit ((7 : ZMod 8831) ^ 4415 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4415 : ZMod 8831)
      decide
    · change IsUnit ((7 : ZMod 8831) ^ 1766 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (615 : ZMod 8831)
      decide
    · change IsUnit ((7 : ZMod 8831) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4744 : ZMod 8831)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8837 : Nat.Prime 8837 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8837 8836 1 2 [2, 2, 47, 47]
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
    · change IsUnit ((2 : ZMod 8837) ^ 4418 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4418 : ZMod 8837)
      decide
    · change IsUnit ((2 : ZMod 8837) ^ 4418 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4418 : ZMod 8837)
      decide
    · change IsUnit ((2 : ZMod 8837) ^ 188 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8274 : ZMod 8837)
      decide
    · change IsUnit ((2 : ZMod 8837) ^ 188 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8274 : ZMod 8837)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8839 : Nat.Prime 8839 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8839 8838 1 3 [2, 3, 3, 491]
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
    · change IsUnit ((3 : ZMod 8839) ^ 4419 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4419 : ZMod 8839)
      decide
    · change IsUnit ((3 : ZMod 8839) ^ 2946 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7381 : ZMod 8839)
      decide
    · change IsUnit ((3 : ZMod 8839) ^ 2946 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7381 : ZMod 8839)
      decide
    · change IsUnit ((3 : ZMod 8839) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1171 : ZMod 8839)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8779) (q := 8783) (by exact lowPrime_8783) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8783) (q := 8803) (by exact lowPrime_8803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8803) (q := 8807) (by exact lowPrime_8807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8807) (q := 8819) (by exact lowPrime_8819) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8819) (q := 8821) (by exact lowPrime_8821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8821) (q := 8831) (by exact lowPrime_8831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8831) (q := 8837) (by exact lowPrime_8837) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8837) (q := 8839) (by exact lowPrime_8839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part05_chain :
    DusartPrimeRowsChain 8779 8839 dusartPrimeRows_8521_8962_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num
