import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 80 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_8329 : Nat.Prime 8329 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8329 8328 1 7 [2, 2, 2, 3, 347]
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
    · change IsUnit ((7 : ZMod 8329) ^ 4164 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4164 : ZMod 8329)
      decide
    · change IsUnit ((7 : ZMod 8329) ^ 4164 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4164 : ZMod 8329)
      decide
    · change IsUnit ((7 : ZMod 8329) ^ 4164 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4164 : ZMod 8329)
      decide
    · change IsUnit ((7 : ZMod 8329) ^ 2776 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5903 : ZMod 8329)
      decide
    · change IsUnit ((7 : ZMod 8329) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4312 : ZMod 8329)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8353 : Nat.Prime 8353 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8353 8352 1 5 [2, 2, 2, 2, 2, 3, 3, 29]
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
    · change IsUnit ((5 : ZMod 8353) ^ 4176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4176 : ZMod 8353)
      decide
    · change IsUnit ((5 : ZMod 8353) ^ 4176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4176 : ZMod 8353)
      decide
    · change IsUnit ((5 : ZMod 8353) ^ 4176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4176 : ZMod 8353)
      decide
    · change IsUnit ((5 : ZMod 8353) ^ 4176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4176 : ZMod 8353)
      decide
    · change IsUnit ((5 : ZMod 8353) ^ 4176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4176 : ZMod 8353)
      decide
    · change IsUnit ((5 : ZMod 8353) ^ 2784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2205 : ZMod 8353)
      decide
    · change IsUnit ((5 : ZMod 8353) ^ 2784 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2205 : ZMod 8353)
      decide
    · change IsUnit ((5 : ZMod 8353) ^ 288 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8320 : ZMod 8353)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8363 : Nat.Prime 8363 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8363 8362 1 2 [2, 37, 113]
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
    · change IsUnit ((2 : ZMod 8363) ^ 4181 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4181 : ZMod 8363)
      decide
    · change IsUnit ((2 : ZMod 8363) ^ 226 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6983 : ZMod 8363)
      decide
    · change IsUnit ((2 : ZMod 8363) ^ 74 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7763 : ZMod 8363)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8369 : Nat.Prime 8369 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8369 8368 1 3 [2, 2, 2, 2, 523]
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
    · change IsUnit ((3 : ZMod 8369) ^ 4184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4184 : ZMod 8369)
      decide
    · change IsUnit ((3 : ZMod 8369) ^ 4184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4184 : ZMod 8369)
      decide
    · change IsUnit ((3 : ZMod 8369) ^ 4184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4184 : ZMod 8369)
      decide
    · change IsUnit ((3 : ZMod 8369) ^ 4184 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4184 : ZMod 8369)
      decide
    · change IsUnit ((3 : ZMod 8369) ^ 16 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2080 : ZMod 8369)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8377 : Nat.Prime 8377 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8377 8376 1 5 [2, 2, 2, 3, 349]
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
    · change IsUnit ((5 : ZMod 8377) ^ 4188 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4188 : ZMod 8377)
      decide
    · change IsUnit ((5 : ZMod 8377) ^ 4188 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4188 : ZMod 8377)
      decide
    · change IsUnit ((5 : ZMod 8377) ^ 4188 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4188 : ZMod 8377)
      decide
    · change IsUnit ((5 : ZMod 8377) ^ 2792 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5313 : ZMod 8377)
      decide
    · change IsUnit ((5 : ZMod 8377) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2759 : ZMod 8377)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8387 : Nat.Prime 8387 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8387 8386 1 2 [2, 7, 599]
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
    · change IsUnit ((2 : ZMod 8387) ^ 4193 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4193 : ZMod 8387)
      decide
    · change IsUnit ((2 : ZMod 8387) ^ 1198 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6456 : ZMod 8387)
      decide
    · change IsUnit ((2 : ZMod 8387) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (429 : ZMod 8387)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8389 : Nat.Prime 8389 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8389 8388 1 6 [2, 2, 3, 3, 233]
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
    · change IsUnit ((6 : ZMod 8389) ^ 4194 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4194 : ZMod 8389)
      decide
    · change IsUnit ((6 : ZMod 8389) ^ 4194 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4194 : ZMod 8389)
      decide
    · change IsUnit ((6 : ZMod 8389) ^ 2796 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8158 : ZMod 8389)
      decide
    · change IsUnit ((6 : ZMod 8389) ^ 2796 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8158 : ZMod 8389)
      decide
    · change IsUnit ((6 : ZMod 8389) ^ 36 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1599 : ZMod 8389)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8419 : Nat.Prime 8419 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8419 8418 1 3 [2, 3, 23, 61]
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
    · change IsUnit ((3 : ZMod 8419) ^ 4209 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4209 : ZMod 8419)
      decide
    · change IsUnit ((3 : ZMod 8419) ^ 2806 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2152 : ZMod 8419)
      decide
    · change IsUnit ((3 : ZMod 8419) ^ 366 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5744 : ZMod 8419)
      decide
    · change IsUnit ((3 : ZMod 8419) ^ 138 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8029 : ZMod 8419)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8317) (q := 8329) (by exact lowPrime_8329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8329) (q := 8353) (by exact lowPrime_8353) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8353) (q := 8363) (by exact lowPrime_8363) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8363) (q := 8369) (by exact lowPrime_8369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8369) (q := 8377) (by exact lowPrime_8377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8377) (q := 8387) (by exact lowPrime_8387) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8387) (q := 8389) (by exact lowPrime_8389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8389) (q := 8419) (by exact lowPrime_8419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part04_chain :
    DusartPrimeRowsChain 8317 8419 dusartPrimeRows_8111_8520_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num
