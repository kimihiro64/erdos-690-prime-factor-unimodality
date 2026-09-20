import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 221 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_21121 : Nat.Prime 21121 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21121 21120 1 19 [2, 2, 2, 2, 2, 2, 2, 3, 5, 11]
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
    · change IsUnit ((19 : ZMod 21121) ^ 10560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10560 : ZMod 21121)
      decide
    · change IsUnit ((19 : ZMod 21121) ^ 10560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10560 : ZMod 21121)
      decide
    · change IsUnit ((19 : ZMod 21121) ^ 10560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10560 : ZMod 21121)
      decide
    · change IsUnit ((19 : ZMod 21121) ^ 10560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10560 : ZMod 21121)
      decide
    · change IsUnit ((19 : ZMod 21121) ^ 10560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10560 : ZMod 21121)
      decide
    · change IsUnit ((19 : ZMod 21121) ^ 10560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10560 : ZMod 21121)
      decide
    · change IsUnit ((19 : ZMod 21121) ^ 10560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10560 : ZMod 21121)
      decide
    · change IsUnit ((19 : ZMod 21121) ^ 7040 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2389 : ZMod 21121)
      decide
    · change IsUnit ((19 : ZMod 21121) ^ 4224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9902 : ZMod 21121)
      decide
    · change IsUnit ((19 : ZMod 21121) ^ 1920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11164 : ZMod 21121)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21139 : Nat.Prime 21139 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21139 21138 1 2 [2, 3, 13, 271]
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
    · change IsUnit ((2 : ZMod 21139) ^ 10569 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10569 : ZMod 21139)
      decide
    · change IsUnit ((2 : ZMod 21139) ^ 7046 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18266 : ZMod 21139)
      decide
    · change IsUnit ((2 : ZMod 21139) ^ 1626 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12453 : ZMod 21139)
      decide
    · change IsUnit ((2 : ZMod 21139) ^ 78 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10898 : ZMod 21139)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21143 : Nat.Prime 21143 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21143 21142 1 10 [2, 11, 31, 31]
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
    · change IsUnit ((10 : ZMod 21143) ^ 10571 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10571 : ZMod 21143)
      decide
    · change IsUnit ((10 : ZMod 21143) ^ 1922 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18834 : ZMod 21143)
      decide
    · change IsUnit ((10 : ZMod 21143) ^ 682 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17618 : ZMod 21143)
      decide
    · change IsUnit ((10 : ZMod 21143) ^ 682 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17618 : ZMod 21143)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21149 : Nat.Prime 21149 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21149 21148 1 3 [2, 2, 17, 311]
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
    · change IsUnit ((3 : ZMod 21149) ^ 10574 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10574 : ZMod 21149)
      decide
    · change IsUnit ((3 : ZMod 21149) ^ 10574 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10574 : ZMod 21149)
      decide
    · change IsUnit ((3 : ZMod 21149) ^ 1244 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10869 : ZMod 21149)
      decide
    · change IsUnit ((3 : ZMod 21149) ^ 68 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17833 : ZMod 21149)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21157 : Nat.Prime 21157 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21157 21156 1 2 [2, 2, 3, 41, 43]
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
    · change IsUnit ((2 : ZMod 21157) ^ 10578 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10578 : ZMod 21157)
      decide
    · change IsUnit ((2 : ZMod 21157) ^ 10578 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10578 : ZMod 21157)
      decide
    · change IsUnit ((2 : ZMod 21157) ^ 7052 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12964 : ZMod 21157)
      decide
    · change IsUnit ((2 : ZMod 21157) ^ 516 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14634 : ZMod 21157)
      decide
    · change IsUnit ((2 : ZMod 21157) ^ 492 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9862 : ZMod 21157)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21163 : Nat.Prime 21163 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21163 21162 1 2 [2, 3, 3527]
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
    · change IsUnit ((2 : ZMod 21163) ^ 10581 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10581 : ZMod 21163)
      decide
    · change IsUnit ((2 : ZMod 21163) ^ 7054 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15554 : ZMod 21163)
      decide
    · change IsUnit ((2 : ZMod 21163) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12765 : ZMod 21163)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21169 : Nat.Prime 21169 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21169 21168 1 13 [2, 2, 2, 2, 3, 3, 3, 7, 7]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((13 : ZMod 21169) ^ 10584 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10584 : ZMod 21169)
      decide
    · change IsUnit ((13 : ZMod 21169) ^ 10584 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10584 : ZMod 21169)
      decide
    · change IsUnit ((13 : ZMod 21169) ^ 10584 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10584 : ZMod 21169)
      decide
    · change IsUnit ((13 : ZMod 21169) ^ 10584 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10584 : ZMod 21169)
      decide
    · change IsUnit ((13 : ZMod 21169) ^ 7056 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10542 : ZMod 21169)
      decide
    · change IsUnit ((13 : ZMod 21169) ^ 7056 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10542 : ZMod 21169)
      decide
    · change IsUnit ((13 : ZMod 21169) ^ 7056 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10542 : ZMod 21169)
      decide
    · change IsUnit ((13 : ZMod 21169) ^ 3024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17432 : ZMod 21169)
      decide
    · change IsUnit ((13 : ZMod 21169) ^ 3024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17432 : ZMod 21169)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21179 : Nat.Prime 21179 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21179 21178 1 2 [2, 10589]
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
    · change IsUnit ((2 : ZMod 21179) ^ 10589 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10589 : ZMod 21179)
      decide
    · change IsUnit ((2 : ZMod 21179) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7060 : ZMod 21179)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21107) (q := 21121) (by exact lowPrime_21121) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21121) (q := 21139) (by exact lowPrime_21139) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21139) (q := 21143) (by exact lowPrime_21143) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21143) (q := 21149) (by exact lowPrime_21149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21149) (q := 21157) (by exact lowPrime_21157) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21157) (q := 21163) (by exact lowPrime_21163) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21163) (q := 21169) (by exact lowPrime_21169) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21169) (q := 21179) (by exact lowPrime_21179) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part03_chain :
    DusartPrimeRowsChain 21107 21179 dusartPrimeRows_20959_22026_part03 := by
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
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num
