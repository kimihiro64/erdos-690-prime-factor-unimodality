import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 108 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10223 : Nat.Prime 10223 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10223 10222 1 5 [2, 19, 269]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5111 : ZMod 10223)
      decide
    · apply IsUnit.of_mul_eq_one (7259 : ZMod 10223)
      decide
    · apply IsUnit.of_mul_eq_one (5490 : ZMod 10223)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10243 : Nat.Prime 10243 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10243 10242 1 7 [2, 3, 3, 569]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5121 : ZMod 10243)
      decide
    · apply IsUnit.of_mul_eq_one (7016 : ZMod 10243)
      decide
    · apply IsUnit.of_mul_eq_one (1942 : ZMod 10243)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10247 : Nat.Prime 10247 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10247 10246 1 5 [2, 47, 109]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5123 : ZMod 10247)
      decide
    · apply IsUnit.of_mul_eq_one (4336 : ZMod 10247)
      decide
    · apply IsUnit.of_mul_eq_one (7615 : ZMod 10247)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10253 : Nat.Prime 10253 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10253 10252 1 2 [2, 2, 11, 233]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5126 : ZMod 10253)
      decide
    · apply IsUnit.of_mul_eq_one (2273 : ZMod 10253)
      decide
    · apply IsUnit.of_mul_eq_one (9846 : ZMod 10253)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10259 : Nat.Prime 10259 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10259 10258 1 2 [2, 23, 223]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5129 : ZMod 10259)
      decide
    · apply IsUnit.of_mul_eq_one (844 : ZMod 10259)
      decide
    · apply IsUnit.of_mul_eq_one (3520 : ZMod 10259)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10267 : Nat.Prime 10267 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10267 10266 1 2 [2, 3, 29, 59]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5133 : ZMod 10267)
      decide
    · apply IsUnit.of_mul_eq_one (58 : ZMod 10267)
      decide
    · apply IsUnit.of_mul_eq_one (2860 : ZMod 10267)
      decide
    · apply IsUnit.of_mul_eq_one (2107 : ZMod 10267)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10271 : Nat.Prime 10271 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10271 10270 1 7 [2, 5, 13, 79]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5135 : ZMod 10271)
      decide
    · apply IsUnit.of_mul_eq_one (9601 : ZMod 10271)
      decide
    · apply IsUnit.of_mul_eq_one (2070 : ZMod 10271)
      decide
    · apply IsUnit.of_mul_eq_one (9855 : ZMod 10271)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10273 : Nat.Prime 10273 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10273 10272 1 10 [2, 2, 2, 2, 2, 3, 107]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5136 : ZMod 10273)
      decide
    · apply IsUnit.of_mul_eq_one (6175 : ZMod 10273)
      decide
    · apply IsUnit.of_mul_eq_one (1401 : ZMod 10273)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10211) (q := 10223) (by exact lowPrime_10223) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10223) (q := 10243) (by exact lowPrime_10243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10243) (q := 10247) (by exact lowPrime_10247) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10247) (q := 10253) (by exact lowPrime_10253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10253) (q := 10259) (by exact lowPrime_10259) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10259) (q := 10267) (by exact lowPrime_10267) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10267) (q := 10271) (by exact lowPrime_10271) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10271) (q := 10273) (by exact lowPrime_10273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part05_chain :
    DusartPrimeRowsChain 10211 10272 dusartPrimeRows_9901_10426_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]
