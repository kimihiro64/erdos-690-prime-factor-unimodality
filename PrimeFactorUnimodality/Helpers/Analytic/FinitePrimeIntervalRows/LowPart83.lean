import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 83 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_8527 : Nat.Prime 8527 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8527 8526 1 5 [2, 3, 7, 7, 29]
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
    · change IsUnit ((5 : ZMod 8527) ^ 4263 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4263 : ZMod 8527)
      decide
    · change IsUnit ((5 : ZMod 8527) ^ 2842 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3834 : ZMod 8527)
      decide
    · change IsUnit ((5 : ZMod 8527) ^ 1218 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (394 : ZMod 8527)
      decide
    · change IsUnit ((5 : ZMod 8527) ^ 1218 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (394 : ZMod 8527)
      decide
    · change IsUnit ((5 : ZMod 8527) ^ 294 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (744 : ZMod 8527)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8537 : Nat.Prime 8537 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8537 8536 1 3 [2, 2, 2, 11, 97]
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
    · change IsUnit ((3 : ZMod 8537) ^ 4268 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4268 : ZMod 8537)
      decide
    · change IsUnit ((3 : ZMod 8537) ^ 4268 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4268 : ZMod 8537)
      decide
    · change IsUnit ((3 : ZMod 8537) ^ 4268 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4268 : ZMod 8537)
      decide
    · change IsUnit ((3 : ZMod 8537) ^ 776 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (544 : ZMod 8537)
      decide
    · change IsUnit ((3 : ZMod 8537) ^ 88 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7731 : ZMod 8537)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8539 : Nat.Prime 8539 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8539 8538 1 2 [2, 3, 1423]
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
    · change IsUnit ((2 : ZMod 8539) ^ 4269 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4269 : ZMod 8539)
      decide
    · change IsUnit ((2 : ZMod 8539) ^ 2846 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1995 : ZMod 8539)
      decide
    · change IsUnit ((2 : ZMod 8539) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6777 : ZMod 8539)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8543 : Nat.Prime 8543 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8543 8542 1 5 [2, 4271]
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
    · change IsUnit ((5 : ZMod 8543) ^ 4271 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4271 : ZMod 8543)
      decide
    · change IsUnit ((5 : ZMod 8543) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (356 : ZMod 8543)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8563 : Nat.Prime 8563 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8563 8562 1 2 [2, 3, 1427]
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
    · change IsUnit ((2 : ZMod 8563) ^ 4281 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4281 : ZMod 8563)
      decide
    · change IsUnit ((2 : ZMod 8563) ^ 2854 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4767 : ZMod 8563)
      decide
    · change IsUnit ((2 : ZMod 8563) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5165 : ZMod 8563)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8573 : Nat.Prime 8573 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8573 8572 1 2 [2, 2, 2143]
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
    · change IsUnit ((2 : ZMod 8573) ^ 4286 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4286 : ZMod 8573)
      decide
    · change IsUnit ((2 : ZMod 8573) ^ 4286 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4286 : ZMod 8573)
      decide
    · change IsUnit ((2 : ZMod 8573) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7430 : ZMod 8573)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8581 : Nat.Prime 8581 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8581 8580 1 6 [2, 2, 3, 5, 11, 13]
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
    · change IsUnit ((6 : ZMod 8581) ^ 4290 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4290 : ZMod 8581)
      decide
    · change IsUnit ((6 : ZMod 8581) ^ 4290 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4290 : ZMod 8581)
      decide
    · change IsUnit ((6 : ZMod 8581) ^ 2860 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8439 : ZMod 8581)
      decide
    · change IsUnit ((6 : ZMod 8581) ^ 1716 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8084 : ZMod 8581)
      decide
    · change IsUnit ((6 : ZMod 8581) ^ 780 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4069 : ZMod 8581)
      decide
    · change IsUnit ((6 : ZMod 8581) ^ 660 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2714 : ZMod 8581)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8597 : Nat.Prime 8597 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8597 8596 1 2 [2, 2, 7, 307]
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
    · change IsUnit ((2 : ZMod 8597) ^ 4298 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4298 : ZMod 8597)
      decide
    · change IsUnit ((2 : ZMod 8597) ^ 4298 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4298 : ZMod 8597)
      decide
    · change IsUnit ((2 : ZMod 8597) ^ 1228 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7660 : ZMod 8597)
      decide
    · change IsUnit ((2 : ZMod 8597) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8411 : ZMod 8597)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8521) (q := 8527) (by exact lowPrime_8527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8527) (q := 8537) (by exact lowPrime_8537) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8537) (q := 8539) (by exact lowPrime_8539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8539) (q := 8543) (by exact lowPrime_8543) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8543) (q := 8563) (by exact lowPrime_8563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8563) (q := 8573) (by exact lowPrime_8573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8573) (q := 8581) (by exact lowPrime_8581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8581) (q := 8597) (by exact lowPrime_8597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part01_chain :
    DusartPrimeRowsChain 8521 8597 dusartPrimeRows_8521_8962_part01 := by
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
