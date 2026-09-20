import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 206 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_22153 : Nat.Prime 22153 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22153 22152 1 5 [2, 2, 2, 3, 13, 71]
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
    · change IsUnit ((5 : ZMod 22153) ^ 11076 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11076 : ZMod 22153)
      decide
    · change IsUnit ((5 : ZMod 22153) ^ 11076 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11076 : ZMod 22153)
      decide
    · change IsUnit ((5 : ZMod 22153) ^ 11076 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11076 : ZMod 22153)
      decide
    · change IsUnit ((5 : ZMod 22153) ^ 7384 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18623 : ZMod 22153)
      decide
    · change IsUnit ((5 : ZMod 22153) ^ 1704 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17802 : ZMod 22153)
      decide
    · change IsUnit ((5 : ZMod 22153) ^ 312 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10450 : ZMod 22153)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22157 : Nat.Prime 22157 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22157 22156 1 2 [2, 2, 29, 191]
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
    · change IsUnit ((2 : ZMod 22157) ^ 11078 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11078 : ZMod 22157)
      decide
    · change IsUnit ((2 : ZMod 22157) ^ 11078 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11078 : ZMod 22157)
      decide
    · change IsUnit ((2 : ZMod 22157) ^ 764 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13731 : ZMod 22157)
      decide
    · change IsUnit ((2 : ZMod 22157) ^ 116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2913 : ZMod 22157)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22159 : Nat.Prime 22159 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22159 22158 1 6 [2, 3, 3, 1231]
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
    · change IsUnit ((6 : ZMod 22159) ^ 11079 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11079 : ZMod 22159)
      decide
    · change IsUnit ((6 : ZMod 22159) ^ 7386 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8559 : ZMod 22159)
      decide
    · change IsUnit ((6 : ZMod 22159) ^ 7386 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8559 : ZMod 22159)
      decide
    · change IsUnit ((6 : ZMod 22159) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19546 : ZMod 22159)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22171 : Nat.Prime 22171 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22171 22170 1 2 [2, 3, 5, 739]
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
    · change IsUnit ((2 : ZMod 22171) ^ 11085 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11085 : ZMod 22171)
      decide
    · change IsUnit ((2 : ZMod 22171) ^ 7390 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6439 : ZMod 22171)
      decide
    · change IsUnit ((2 : ZMod 22171) ^ 4434 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2686 : ZMod 22171)
      decide
    · change IsUnit ((2 : ZMod 22171) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10972 : ZMod 22171)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22189 : Nat.Prime 22189 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22189 22188 1 2 [2, 2, 3, 43, 43]
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
    · change IsUnit ((2 : ZMod 22189) ^ 11094 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11094 : ZMod 22189)
      decide
    · change IsUnit ((2 : ZMod 22189) ^ 11094 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11094 : ZMod 22189)
      decide
    · change IsUnit ((2 : ZMod 22189) ^ 7396 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11137 : ZMod 22189)
      decide
    · change IsUnit ((2 : ZMod 22189) ^ 516 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7750 : ZMod 22189)
      decide
    · change IsUnit ((2 : ZMod 22189) ^ 516 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7750 : ZMod 22189)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22193 : Nat.Prime 22193 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22193 22192 1 3 [2, 2, 2, 2, 19, 73]
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
    · change IsUnit ((3 : ZMod 22193) ^ 11096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11096 : ZMod 22193)
      decide
    · change IsUnit ((3 : ZMod 22193) ^ 11096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11096 : ZMod 22193)
      decide
    · change IsUnit ((3 : ZMod 22193) ^ 11096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11096 : ZMod 22193)
      decide
    · change IsUnit ((3 : ZMod 22193) ^ 11096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11096 : ZMod 22193)
      decide
    · change IsUnit ((3 : ZMod 22193) ^ 1168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9477 : ZMod 22193)
      decide
    · change IsUnit ((3 : ZMod 22193) ^ 304 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3123 : ZMod 22193)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22229 : Nat.Prime 22229 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22229 22228 1 2 [2, 2, 5557]
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
    · change IsUnit ((2 : ZMod 22229) ^ 11114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11114 : ZMod 22229)
      decide
    · change IsUnit ((2 : ZMod 22229) ^ 11114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11114 : ZMod 22229)
      decide
    · change IsUnit ((2 : ZMod 22229) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1482 : ZMod 22229)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22247 : Nat.Prime 22247 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22247 22246 1 5 [2, 7, 7, 227]
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
    · change IsUnit ((5 : ZMod 22247) ^ 11123 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11123 : ZMod 22247)
      decide
    · change IsUnit ((5 : ZMod 22247) ^ 3178 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2047 : ZMod 22247)
      decide
    · change IsUnit ((5 : ZMod 22247) ^ 3178 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2047 : ZMod 22247)
      decide
    · change IsUnit ((5 : ZMod 22247) ^ 98 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14598 : ZMod 22247)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22147) (q := 22153) (by exact lowPrime_22153) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22153) (q := 22157) (by exact lowPrime_22157) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22157) (q := 22159) (by exact lowPrime_22159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22159) (q := 22171) (by exact lowPrime_22171) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22171) (q := 22189) (by exact lowPrime_22189) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22189) (q := 22193) (by exact lowPrime_22193) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22193) (q := 22229) (by exact lowPrime_22229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22229) (q := 22247) (by exact lowPrime_22247) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part03_chain :
    DusartPrimeRowsChain 22147 22247 dusartPrimeRows_22027_23158_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num
