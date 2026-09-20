import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 99 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_9547 : Nat.Prime 9547 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9547 9546 1 2 [2, 3, 37, 43]
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
    · change IsUnit ((2 : ZMod 9547) ^ 4773 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4773 : ZMod 9547)
      decide
    · change IsUnit ((2 : ZMod 9547) ^ 3182 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8457 : ZMod 9547)
      decide
    · change IsUnit ((2 : ZMod 9547) ^ 258 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1990 : ZMod 9547)
      decide
    · change IsUnit ((2 : ZMod 9547) ^ 222 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7471 : ZMod 9547)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9551 : Nat.Prime 9551 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9551 9550 1 11 [2, 5, 5, 191]
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
    · change IsUnit ((11 : ZMod 9551) ^ 4775 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4775 : ZMod 9551)
      decide
    · change IsUnit ((11 : ZMod 9551) ^ 1910 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1234 : ZMod 9551)
      decide
    · change IsUnit ((11 : ZMod 9551) ^ 1910 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1234 : ZMod 9551)
      decide
    · change IsUnit ((11 : ZMod 9551) ^ 50 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6753 : ZMod 9551)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9587 : Nat.Prime 9587 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9587 9586 1 2 [2, 4793]
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
    · change IsUnit ((2 : ZMod 9587) ^ 4793 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4793 : ZMod 9587)
      decide
    · change IsUnit ((2 : ZMod 9587) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3196 : ZMod 9587)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9601 : Nat.Prime 9601 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9601 9600 1 13 [2, 2, 2, 2, 2, 2, 2, 3, 5, 5]
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
    · change IsUnit ((13 : ZMod 9601) ^ 4800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4800 : ZMod 9601)
      decide
    · change IsUnit ((13 : ZMod 9601) ^ 4800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4800 : ZMod 9601)
      decide
    · change IsUnit ((13 : ZMod 9601) ^ 4800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4800 : ZMod 9601)
      decide
    · change IsUnit ((13 : ZMod 9601) ^ 4800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4800 : ZMod 9601)
      decide
    · change IsUnit ((13 : ZMod 9601) ^ 4800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4800 : ZMod 9601)
      decide
    · change IsUnit ((13 : ZMod 9601) ^ 4800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4800 : ZMod 9601)
      decide
    · change IsUnit ((13 : ZMod 9601) ^ 4800 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4800 : ZMod 9601)
      decide
    · change IsUnit ((13 : ZMod 9601) ^ 3200 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4602 : ZMod 9601)
      decide
    · change IsUnit ((13 : ZMod 9601) ^ 1920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6151 : ZMod 9601)
      decide
    · change IsUnit ((13 : ZMod 9601) ^ 1920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6151 : ZMod 9601)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9613 : Nat.Prime 9613 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9613 9612 1 2 [2, 2, 3, 3, 3, 89]
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
    · change IsUnit ((2 : ZMod 9613) ^ 4806 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4806 : ZMod 9613)
      decide
    · change IsUnit ((2 : ZMod 9613) ^ 4806 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4806 : ZMod 9613)
      decide
    · change IsUnit ((2 : ZMod 9613) ^ 3204 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2175 : ZMod 9613)
      decide
    · change IsUnit ((2 : ZMod 9613) ^ 3204 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2175 : ZMod 9613)
      decide
    · change IsUnit ((2 : ZMod 9613) ^ 3204 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2175 : ZMod 9613)
      decide
    · change IsUnit ((2 : ZMod 9613) ^ 108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7292 : ZMod 9613)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9619 : Nat.Prime 9619 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9619 9618 1 2 [2, 3, 7, 229]
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
    · change IsUnit ((2 : ZMod 9619) ^ 4809 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4809 : ZMod 9619)
      decide
    · change IsUnit ((2 : ZMod 9619) ^ 3206 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1475 : ZMod 9619)
      decide
    · change IsUnit ((2 : ZMod 9619) ^ 1374 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (83 : ZMod 9619)
      decide
    · change IsUnit ((2 : ZMod 9619) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6054 : ZMod 9619)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9623 : Nat.Prime 9623 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9623 9622 1 5 [2, 17, 283]
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
    · change IsUnit ((5 : ZMod 9623) ^ 4811 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4811 : ZMod 9623)
      decide
    · change IsUnit ((5 : ZMod 9623) ^ 566 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3337 : ZMod 9623)
      decide
    · change IsUnit ((5 : ZMod 9623) ^ 34 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1 : ZMod 9623)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9629 : Nat.Prime 9629 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9629 9628 1 2 [2, 2, 29, 83]
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
    · change IsUnit ((2 : ZMod 9629) ^ 4814 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4814 : ZMod 9629)
      decide
    · change IsUnit ((2 : ZMod 9629) ^ 4814 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4814 : ZMod 9629)
      decide
    · change IsUnit ((2 : ZMod 9629) ^ 332 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3835 : ZMod 9629)
      decide
    · change IsUnit ((2 : ZMod 9629) ^ 116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5865 : ZMod 9629)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9539) (q := 9547) (by exact lowPrime_9547) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9547) (q := 9551) (by exact lowPrime_9551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9551) (q := 9587) (by exact lowPrime_9587) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9587) (q := 9601) (by exact lowPrime_9601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9601) (q := 9613) (by exact lowPrime_9613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9613) (q := 9619) (by exact lowPrime_9619) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9619) (q := 9623) (by exact lowPrime_9623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9623) (q := 9629) (by exact lowPrime_9629) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part03_chain :
    DusartPrimeRowsChain 9539 9629 dusartPrimeRows_9419_9900_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num
