import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 237 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_20231 : Nat.Prime 20231 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20231 20230 1 29 [2, 5, 7, 17, 17]
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
    · change IsUnit ((29 : ZMod 20231) ^ 10115 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10115 : ZMod 20231)
      decide
    · change IsUnit ((29 : ZMod 20231) ^ 4046 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1399 : ZMod 20231)
      decide
    · change IsUnit ((29 : ZMod 20231) ^ 2890 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17148 : ZMod 20231)
      decide
    · change IsUnit ((29 : ZMod 20231) ^ 1190 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5337 : ZMod 20231)
      decide
    · change IsUnit ((29 : ZMod 20231) ^ 1190 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5337 : ZMod 20231)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20233 : Nat.Prime 20233 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20233 20232 1 5 [2, 2, 2, 3, 3, 281]
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
    · change IsUnit ((5 : ZMod 20233) ^ 10116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10116 : ZMod 20233)
      decide
    · change IsUnit ((5 : ZMod 20233) ^ 10116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10116 : ZMod 20233)
      decide
    · change IsUnit ((5 : ZMod 20233) ^ 10116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10116 : ZMod 20233)
      decide
    · change IsUnit ((5 : ZMod 20233) ^ 6744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19074 : ZMod 20233)
      decide
    · change IsUnit ((5 : ZMod 20233) ^ 6744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19074 : ZMod 20233)
      decide
    · change IsUnit ((5 : ZMod 20233) ^ 72 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18809 : ZMod 20233)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20249 : Nat.Prime 20249 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20249 20248 1 3 [2, 2, 2, 2531]
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
    · change IsUnit ((3 : ZMod 20249) ^ 10124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10124 : ZMod 20249)
      decide
    · change IsUnit ((3 : ZMod 20249) ^ 10124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10124 : ZMod 20249)
      decide
    · change IsUnit ((3 : ZMod 20249) ^ 10124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10124 : ZMod 20249)
      decide
    · change IsUnit ((3 : ZMod 20249) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4911 : ZMod 20249)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20261 : Nat.Prime 20261 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20261 20260 1 2 [2, 2, 5, 1013]
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
    · change IsUnit ((2 : ZMod 20261) ^ 10130 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10130 : ZMod 20261)
      decide
    · change IsUnit ((2 : ZMod 20261) ^ 10130 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10130 : ZMod 20261)
      decide
    · change IsUnit ((2 : ZMod 20261) ^ 4052 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2364 : ZMod 20261)
      decide
    · change IsUnit ((2 : ZMod 20261) ^ 20 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10984 : ZMod 20261)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20269 : Nat.Prime 20269 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20269 20268 1 2 [2, 2, 3, 3, 563]
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
    · change IsUnit ((2 : ZMod 20269) ^ 10134 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10134 : ZMod 20269)
      decide
    · change IsUnit ((2 : ZMod 20269) ^ 10134 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10134 : ZMod 20269)
      decide
    · change IsUnit ((2 : ZMod 20269) ^ 6756 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4932 : ZMod 20269)
      decide
    · change IsUnit ((2 : ZMod 20269) ^ 6756 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4932 : ZMod 20269)
      decide
    · change IsUnit ((2 : ZMod 20269) ^ 36 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1169 : ZMod 20269)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20287 : Nat.Prime 20287 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20287 20286 1 5 [2, 3, 3, 7, 7, 23]
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
    · change IsUnit ((5 : ZMod 20287) ^ 10143 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10143 : ZMod 20287)
      decide
    · change IsUnit ((5 : ZMod 20287) ^ 6762 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16027 : ZMod 20287)
      decide
    · change IsUnit ((5 : ZMod 20287) ^ 6762 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16027 : ZMod 20287)
      decide
    · change IsUnit ((5 : ZMod 20287) ^ 2898 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8350 : ZMod 20287)
      decide
    · change IsUnit ((5 : ZMod 20287) ^ 2898 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8350 : ZMod 20287)
      decide
    · change IsUnit ((5 : ZMod 20287) ^ 882 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16878 : ZMod 20287)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20297 : Nat.Prime 20297 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20297 20296 1 3 [2, 2, 2, 43, 59]
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
    · change IsUnit ((3 : ZMod 20297) ^ 10148 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10148 : ZMod 20297)
      decide
    · change IsUnit ((3 : ZMod 20297) ^ 10148 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10148 : ZMod 20297)
      decide
    · change IsUnit ((3 : ZMod 20297) ^ 10148 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10148 : ZMod 20297)
      decide
    · change IsUnit ((3 : ZMod 20297) ^ 472 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8084 : ZMod 20297)
      decide
    · change IsUnit ((3 : ZMod 20297) ^ 344 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10825 : ZMod 20297)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20323 : Nat.Prime 20323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20323 20322 1 2 [2, 3, 3, 1129]
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
    · change IsUnit ((2 : ZMod 20323) ^ 10161 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10161 : ZMod 20323)
      decide
    · change IsUnit ((2 : ZMod 20323) ^ 6774 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3301 : ZMod 20323)
      decide
    · change IsUnit ((2 : ZMod 20323) ^ 6774 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3301 : ZMod 20323)
      decide
    · change IsUnit ((2 : ZMod 20323) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3430 : ZMod 20323)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20219) (q := 20231) (by exact lowPrime_20231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20231) (q := 20233) (by exact lowPrime_20233) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20233) (q := 20249) (by exact lowPrime_20249) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20249) (q := 20261) (by exact lowPrime_20261) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20261) (q := 20269) (by exact lowPrime_20269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20269) (q := 20287) (by exact lowPrime_20287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20287) (q := 20297) (by exact lowPrime_20297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20297) (q := 20323) (by exact lowPrime_20323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part05_chain :
    DusartPrimeRowsChain 20219 20323 dusartPrimeRows_19937_20958_part05 := by
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
