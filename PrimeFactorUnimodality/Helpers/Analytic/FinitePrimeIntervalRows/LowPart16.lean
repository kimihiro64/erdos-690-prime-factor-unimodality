import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 16 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_4219 : Nat.Prime 4219 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4219 4218 1 2 [2, 3, 19, 37]
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
    · change IsUnit ((2 : ZMod 4219) ^ 2109 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2109 : ZMod 4219)
      decide
    · change IsUnit ((2 : ZMod 4219) ^ 1406 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4181 : ZMod 4219)
      decide
    · change IsUnit ((2 : ZMod 4219) ^ 222 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1998 : ZMod 4219)
      decide
    · change IsUnit ((2 : ZMod 4219) ^ 114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (673 : ZMod 4219)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4229 : Nat.Prime 4229 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4229 4228 1 2 [2, 2, 7, 151]
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
    · change IsUnit ((2 : ZMod 4229) ^ 2114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2114 : ZMod 4229)
      decide
    · change IsUnit ((2 : ZMod 4229) ^ 2114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2114 : ZMod 4229)
      decide
    · change IsUnit ((2 : ZMod 4229) ^ 604 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (129 : ZMod 4229)
      decide
    · change IsUnit ((2 : ZMod 4229) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3555 : ZMod 4229)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4231 : Nat.Prime 4231 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4231 4230 1 3 [2, 3, 3, 5, 47]
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
    · change IsUnit ((3 : ZMod 4231) ^ 2115 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2115 : ZMod 4231)
      decide
    · change IsUnit ((3 : ZMod 4231) ^ 1410 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3027 : ZMod 4231)
      decide
    · change IsUnit ((3 : ZMod 4231) ^ 1410 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3027 : ZMod 4231)
      decide
    · change IsUnit ((3 : ZMod 4231) ^ 846 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (236 : ZMod 4231)
      decide
    · change IsUnit ((3 : ZMod 4231) ^ 90 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1140 : ZMod 4231)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4241 : Nat.Prime 4241 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4241 4240 1 3 [2, 2, 2, 2, 5, 53]
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
    · change IsUnit ((3 : ZMod 4241) ^ 2120 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2120 : ZMod 4241)
      decide
    · change IsUnit ((3 : ZMod 4241) ^ 2120 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2120 : ZMod 4241)
      decide
    · change IsUnit ((3 : ZMod 4241) ^ 2120 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2120 : ZMod 4241)
      decide
    · change IsUnit ((3 : ZMod 4241) ^ 2120 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2120 : ZMod 4241)
      decide
    · change IsUnit ((3 : ZMod 4241) ^ 848 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (575 : ZMod 4241)
      decide
    · change IsUnit ((3 : ZMod 4241) ^ 80 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2244 : ZMod 4241)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4243 : Nat.Prime 4243 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4243 4242 1 2 [2, 3, 7, 101]
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
    · change IsUnit ((2 : ZMod 4243) ^ 2121 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2121 : ZMod 4243)
      decide
    · change IsUnit ((2 : ZMod 4243) ^ 1414 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4143 : ZMod 4243)
      decide
    · change IsUnit ((2 : ZMod 4243) ^ 606 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3750 : ZMod 4243)
      decide
    · change IsUnit ((2 : ZMod 4243) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4131 : ZMod 4243)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4253 : Nat.Prime 4253 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4253 4252 1 2 [2, 2, 1063]
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
    · change IsUnit ((2 : ZMod 4253) ^ 2126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2126 : ZMod 4253)
      decide
    · change IsUnit ((2 : ZMod 4253) ^ 2126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2126 : ZMod 4253)
      decide
    · change IsUnit ((2 : ZMod 4253) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3686 : ZMod 4253)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4259 : Nat.Prime 4259 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4259 4258 1 2 [2, 2129]
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
    · change IsUnit ((2 : ZMod 4259) ^ 2129 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2129 : ZMod 4259)
      decide
    · change IsUnit ((2 : ZMod 4259) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1420 : ZMod 4259)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4261 : Nat.Prime 4261 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4261 4260 1 2 [2, 2, 3, 5, 71]
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
    · change IsUnit ((2 : ZMod 4261) ^ 2130 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2130 : ZMod 4261)
      decide
    · change IsUnit ((2 : ZMod 4261) ^ 2130 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2130 : ZMod 4261)
      decide
    · change IsUnit ((2 : ZMod 4261) ^ 1420 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2291 : ZMod 4261)
      decide
    · change IsUnit ((2 : ZMod 4261) ^ 852 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2211 : ZMod 4261)
      decide
    · change IsUnit ((2 : ZMod 4261) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2269 : ZMod 4261)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4217) (q := 4219) (by exact lowPrime_4219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4219) (q := 4229) (by exact lowPrime_4229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4229) (q := 4231) (by exact lowPrime_4231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4231) (q := 4241) (by exact lowPrime_4241) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4241) (q := 4243) (by exact lowPrime_4243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4243) (q := 4253) (by exact lowPrime_4253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4253) (q := 4259) (by exact lowPrime_4259) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4259) (q := 4261) (by exact lowPrime_4261) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part07_chain :
    DusartPrimeRowsChain 4217 4261 dusartPrimeRows_3803_4672_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num
