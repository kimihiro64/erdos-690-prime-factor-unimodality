import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 239 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_20389 : Nat.Prime 20389 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20389 20388 1 6 [2, 2, 3, 1699]
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
    · change IsUnit ((6 : ZMod 20389) ^ 10194 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10194 : ZMod 20389)
      decide
    · change IsUnit ((6 : ZMod 20389) ^ 10194 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10194 : ZMod 20389)
      decide
    · change IsUnit ((6 : ZMod 20389) ^ 6796 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7588 : ZMod 20389)
      decide
    · change IsUnit ((6 : ZMod 20389) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9215 : ZMod 20389)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20393 : Nat.Prime 20393 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20393 20392 1 3 [2, 2, 2, 2549]
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
    · change IsUnit ((3 : ZMod 20393) ^ 10196 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10196 : ZMod 20393)
      decide
    · change IsUnit ((3 : ZMod 20393) ^ 10196 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10196 : ZMod 20393)
      decide
    · change IsUnit ((3 : ZMod 20393) ^ 10196 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10196 : ZMod 20393)
      decide
    · change IsUnit ((3 : ZMod 20393) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10268 : ZMod 20393)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20399 : Nat.Prime 20399 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20399 20398 1 7 [2, 7, 31, 47]
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
    · change IsUnit ((7 : ZMod 20399) ^ 10199 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10199 : ZMod 20399)
      decide
    · change IsUnit ((7 : ZMod 20399) ^ 2914 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10839 : ZMod 20399)
      decide
    · change IsUnit ((7 : ZMod 20399) ^ 658 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18124 : ZMod 20399)
      decide
    · change IsUnit ((7 : ZMod 20399) ^ 434 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11188 : ZMod 20399)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20407 : Nat.Prime 20407 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20407 20406 1 5 [2, 3, 19, 179]
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
    · change IsUnit ((5 : ZMod 20407) ^ 10203 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10203 : ZMod 20407)
      decide
    · change IsUnit ((5 : ZMod 20407) ^ 6802 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11712 : ZMod 20407)
      decide
    · change IsUnit ((5 : ZMod 20407) ^ 1074 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17961 : ZMod 20407)
      decide
    · change IsUnit ((5 : ZMod 20407) ^ 114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14218 : ZMod 20407)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20411 : Nat.Prime 20411 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20411 20410 1 6 [2, 5, 13, 157]
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
    · change IsUnit ((6 : ZMod 20411) ^ 10205 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10205 : ZMod 20411)
      decide
    · change IsUnit ((6 : ZMod 20411) ^ 4082 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4446 : ZMod 20411)
      decide
    · change IsUnit ((6 : ZMod 20411) ^ 1570 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9910 : ZMod 20411)
      decide
    · change IsUnit ((6 : ZMod 20411) ^ 130 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12686 : ZMod 20411)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20431 : Nat.Prime 20431 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20431 20430 1 3 [2, 3, 3, 5, 227]
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
    · change IsUnit ((3 : ZMod 20431) ^ 10215 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10215 : ZMod 20431)
      decide
    · change IsUnit ((3 : ZMod 20431) ^ 6810 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2930 : ZMod 20431)
      decide
    · change IsUnit ((3 : ZMod 20431) ^ 6810 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2930 : ZMod 20431)
      decide
    · change IsUnit ((3 : ZMod 20431) ^ 4086 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1686 : ZMod 20431)
      decide
    · change IsUnit ((3 : ZMod 20431) ^ 90 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2635 : ZMod 20431)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20441 : Nat.Prime 20441 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20441 20440 1 3 [2, 2, 2, 5, 7, 73]
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
    · change IsUnit ((3 : ZMod 20441) ^ 10220 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10220 : ZMod 20441)
      decide
    · change IsUnit ((3 : ZMod 20441) ^ 10220 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10220 : ZMod 20441)
      decide
    · change IsUnit ((3 : ZMod 20441) ^ 10220 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10220 : ZMod 20441)
      decide
    · change IsUnit ((3 : ZMod 20441) ^ 4088 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16809 : ZMod 20441)
      decide
    · change IsUnit ((3 : ZMod 20441) ^ 2920 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (432 : ZMod 20441)
      decide
    · change IsUnit ((3 : ZMod 20441) ^ 280 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13826 : ZMod 20441)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20443 : Nat.Prime 20443 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20443 20442 1 2 [2, 3, 3407]
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
    · change IsUnit ((2 : ZMod 20443) ^ 10221 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10221 : ZMod 20443)
      decide
    · change IsUnit ((2 : ZMod 20443) ^ 6814 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19114 : ZMod 20443)
      decide
    · change IsUnit ((2 : ZMod 20443) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (649 : ZMod 20443)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20369) (q := 20389) (by exact lowPrime_20389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20389) (q := 20393) (by exact lowPrime_20393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20393) (q := 20399) (by exact lowPrime_20399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20399) (q := 20407) (by exact lowPrime_20407) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20407) (q := 20411) (by exact lowPrime_20411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20411) (q := 20431) (by exact lowPrime_20431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20431) (q := 20441) (by exact lowPrime_20441) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20441) (q := 20443) (by exact lowPrime_20443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part07_chain :
    DusartPrimeRowsChain 20369 20443 dusartPrimeRows_19937_20958_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · apply DusartPrimeRowsChain.empty
                  norm_num
