import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 111 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_10429 : Nat.Prime 10429 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10429 10428 1 7 [2, 2, 3, 11, 79]
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
    · change IsUnit ((7 : ZMod 10429) ^ 5214 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5214 : ZMod 10429)
      decide
    · change IsUnit ((7 : ZMod 10429) ^ 5214 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5214 : ZMod 10429)
      decide
    · change IsUnit ((7 : ZMod 10429) ^ 3476 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2671 : ZMod 10429)
      decide
    · change IsUnit ((7 : ZMod 10429) ^ 948 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1266 : ZMod 10429)
      decide
    · change IsUnit ((7 : ZMod 10429) ^ 132 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6072 : ZMod 10429)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10433 : Nat.Prime 10433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10433 10432 1 3 [2, 2, 2, 2, 2, 2, 163]
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
    · change IsUnit ((3 : ZMod 10433) ^ 5216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5216 : ZMod 10433)
      decide
    · change IsUnit ((3 : ZMod 10433) ^ 5216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5216 : ZMod 10433)
      decide
    · change IsUnit ((3 : ZMod 10433) ^ 5216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5216 : ZMod 10433)
      decide
    · change IsUnit ((3 : ZMod 10433) ^ 5216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5216 : ZMod 10433)
      decide
    · change IsUnit ((3 : ZMod 10433) ^ 5216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5216 : ZMod 10433)
      decide
    · change IsUnit ((3 : ZMod 10433) ^ 5216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5216 : ZMod 10433)
      decide
    · change IsUnit ((3 : ZMod 10433) ^ 64 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10059 : ZMod 10433)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10453 : Nat.Prime 10453 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10453 10452 1 5 [2, 2, 3, 13, 67]
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
    · change IsUnit ((5 : ZMod 10453) ^ 5226 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5226 : ZMod 10453)
      decide
    · change IsUnit ((5 : ZMod 10453) ^ 5226 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5226 : ZMod 10453)
      decide
    · change IsUnit ((5 : ZMod 10453) ^ 3484 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3574 : ZMod 10453)
      decide
    · change IsUnit ((5 : ZMod 10453) ^ 804 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2912 : ZMod 10453)
      decide
    · change IsUnit ((5 : ZMod 10453) ^ 156 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2197 : ZMod 10453)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10457 : Nat.Prime 10457 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10457 10456 1 3 [2, 2, 2, 1307]
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
    · change IsUnit ((3 : ZMod 10457) ^ 5228 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5228 : ZMod 10457)
      decide
    · change IsUnit ((3 : ZMod 10457) ^ 5228 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5228 : ZMod 10457)
      decide
    · change IsUnit ((3 : ZMod 10457) ^ 5228 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5228 : ZMod 10457)
      decide
    · change IsUnit ((3 : ZMod 10457) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7025 : ZMod 10457)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10459 : Nat.Prime 10459 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10459 10458 1 2 [2, 3, 3, 7, 83]
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
    · change IsUnit ((2 : ZMod 10459) ^ 5229 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5229 : ZMod 10459)
      decide
    · change IsUnit ((2 : ZMod 10459) ^ 3486 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3929 : ZMod 10459)
      decide
    · change IsUnit ((2 : ZMod 10459) ^ 3486 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3929 : ZMod 10459)
      decide
    · change IsUnit ((2 : ZMod 10459) ^ 1494 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6060 : ZMod 10459)
      decide
    · change IsUnit ((2 : ZMod 10459) ^ 126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7039 : ZMod 10459)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10463 : Nat.Prime 10463 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10463 10462 1 5 [2, 5231]
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
    · change IsUnit ((5 : ZMod 10463) ^ 5231 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5231 : ZMod 10463)
      decide
    · change IsUnit ((5 : ZMod 10463) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (436 : ZMod 10463)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10477 : Nat.Prime 10477 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10477 10476 1 2 [2, 2, 3, 3, 3, 97]
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
    · change IsUnit ((2 : ZMod 10477) ^ 5238 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5238 : ZMod 10477)
      decide
    · change IsUnit ((2 : ZMod 10477) ^ 5238 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5238 : ZMod 10477)
      decide
    · change IsUnit ((2 : ZMod 10477) ^ 3492 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3253 : ZMod 10477)
      decide
    · change IsUnit ((2 : ZMod 10477) ^ 3492 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3253 : ZMod 10477)
      decide
    · change IsUnit ((2 : ZMod 10477) ^ 3492 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3253 : ZMod 10477)
      decide
    · change IsUnit ((2 : ZMod 10477) ^ 108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (278 : ZMod 10477)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10487 : Nat.Prime 10487 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10487 10486 1 5 [2, 7, 7, 107]
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
    · change IsUnit ((5 : ZMod 10487) ^ 5243 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5243 : ZMod 10487)
      decide
    · change IsUnit ((5 : ZMod 10487) ^ 1498 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7871 : ZMod 10487)
      decide
    · change IsUnit ((5 : ZMod 10487) ^ 1498 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7871 : ZMod 10487)
      decide
    · change IsUnit ((5 : ZMod 10487) ^ 98 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7201 : ZMod 10487)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10427) (q := 10429) (by exact lowPrime_10429) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10429) (q := 10433) (by exact lowPrime_10433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10433) (q := 10453) (by exact lowPrime_10453) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10453) (q := 10457) (by exact lowPrime_10457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10457) (q := 10459) (by exact lowPrime_10459) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10459) (q := 10463) (by exact lowPrime_10463) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10463) (q := 10477) (by exact lowPrime_10477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10477) (q := 10487) (by exact lowPrime_10487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part01_chain :
    DusartPrimeRowsChain 10427 10487 dusartPrimeRows_10427_10938_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10938]
              · norm_num [dusartPrimeRow_of_explicit_10938]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10938]
                · norm_num [dusartPrimeRow_of_explicit_10938]
                · apply DusartPrimeRowsChain.empty
                  norm_num
