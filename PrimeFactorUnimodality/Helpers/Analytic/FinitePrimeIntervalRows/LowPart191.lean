import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 191 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_16223 : Nat.Prime 16223 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16223 16222 1 5 [2, 8111]
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
    · change IsUnit ((5 : ZMod 16223) ^ 8111 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8111 : ZMod 16223)
      decide
    · change IsUnit ((5 : ZMod 16223) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (676 : ZMod 16223)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16229 : Nat.Prime 16229 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16229 16228 1 2 [2, 2, 4057]
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
    · change IsUnit ((2 : ZMod 16229) ^ 8114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8114 : ZMod 16229)
      decide
    · change IsUnit ((2 : ZMod 16229) ^ 8114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8114 : ZMod 16229)
      decide
    · change IsUnit ((2 : ZMod 16229) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1082 : ZMod 16229)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16231 : Nat.Prime 16231 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16231 16230 1 3 [2, 3, 5, 541]
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
    · change IsUnit ((3 : ZMod 16231) ^ 8115 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8115 : ZMod 16231)
      decide
    · change IsUnit ((3 : ZMod 16231) ^ 5410 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12835 : ZMod 16231)
      decide
    · change IsUnit ((3 : ZMod 16231) ^ 3246 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5001 : ZMod 16231)
      decide
    · change IsUnit ((3 : ZMod 16231) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1376 : ZMod 16231)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16249 : Nat.Prime 16249 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16249 16248 1 17 [2, 2, 2, 3, 677]
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
    · change IsUnit ((17 : ZMod 16249) ^ 8124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8124 : ZMod 16249)
      decide
    · change IsUnit ((17 : ZMod 16249) ^ 8124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8124 : ZMod 16249)
      decide
    · change IsUnit ((17 : ZMod 16249) ^ 8124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8124 : ZMod 16249)
      decide
    · change IsUnit ((17 : ZMod 16249) ^ 5416 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13743 : ZMod 16249)
      decide
    · change IsUnit ((17 : ZMod 16249) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15902 : ZMod 16249)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16253 : Nat.Prime 16253 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16253 16252 1 2 [2, 2, 17, 239]
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
    · change IsUnit ((2 : ZMod 16253) ^ 8126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8126 : ZMod 16253)
      decide
    · change IsUnit ((2 : ZMod 16253) ^ 8126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8126 : ZMod 16253)
      decide
    · change IsUnit ((2 : ZMod 16253) ^ 956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13171 : ZMod 16253)
      decide
    · change IsUnit ((2 : ZMod 16253) ^ 68 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6135 : ZMod 16253)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16267 : Nat.Prime 16267 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16267 16266 1 3 [2, 3, 2711]
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
    · change IsUnit ((3 : ZMod 16267) ^ 8133 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8133 : ZMod 16267)
      decide
    · change IsUnit ((3 : ZMod 16267) ^ 5422 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (265 : ZMod 16267)
      decide
    · change IsUnit ((3 : ZMod 16267) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (648 : ZMod 16267)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16273 : Nat.Prime 16273 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16273 16272 1 7 [2, 2, 2, 2, 3, 3, 113]
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
    · change IsUnit ((7 : ZMod 16273) ^ 8136 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8136 : ZMod 16273)
      decide
    · change IsUnit ((7 : ZMod 16273) ^ 8136 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8136 : ZMod 16273)
      decide
    · change IsUnit ((7 : ZMod 16273) ^ 8136 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8136 : ZMod 16273)
      decide
    · change IsUnit ((7 : ZMod 16273) ^ 8136 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8136 : ZMod 16273)
      decide
    · change IsUnit ((7 : ZMod 16273) ^ 5424 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9133 : ZMod 16273)
      decide
    · change IsUnit ((7 : ZMod 16273) ^ 5424 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9133 : ZMod 16273)
      decide
    · change IsUnit ((7 : ZMod 16273) ^ 144 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1231 : ZMod 16273)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16301 : Nat.Prime 16301 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16301 16300 1 2 [2, 2, 5, 5, 163]
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
    · change IsUnit ((2 : ZMod 16301) ^ 8150 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8150 : ZMod 16301)
      decide
    · change IsUnit ((2 : ZMod 16301) ^ 8150 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8150 : ZMod 16301)
      decide
    · change IsUnit ((2 : ZMod 16301) ^ 3260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12873 : ZMod 16301)
      decide
    · change IsUnit ((2 : ZMod 16301) ^ 3260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12873 : ZMod 16301)
      decide
    · change IsUnit ((2 : ZMod 16301) ^ 100 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10036 : ZMod 16301)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 16217) (q := 16223) (by exact lowPrime_16223) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16223) (q := 16229) (by exact lowPrime_16229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16229) (q := 16231) (by exact lowPrime_16231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16231) (q := 16249) (by exact lowPrime_16249) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16249) (q := 16253) (by exact lowPrime_16253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16253) (q := 16267) (by exact lowPrime_16267) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16267) (q := 16273) (by exact lowPrime_16273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16273) (q := 16301) (by exact lowPrime_16301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part10_chain :
    DusartPrimeRowsChain 16217 16301 dusartPrimeRows_15527_16318_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · apply DusartPrimeRowsChain.empty
                  norm_num
