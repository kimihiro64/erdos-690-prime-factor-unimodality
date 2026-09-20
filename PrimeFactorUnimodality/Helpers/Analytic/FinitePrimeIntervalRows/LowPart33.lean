import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 33 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5323 : Nat.Prime 5323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5323 5322 1 5 [2, 3, 887]
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
    · apply IsUnit.of_mul_eq_one (2661 : ZMod 5323)
      decide
    · apply IsUnit.of_mul_eq_one (4895 : ZMod 5323)
      decide
    · apply IsUnit.of_mul_eq_one (108 : ZMod 5323)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5333 : Nat.Prime 5333 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5333 5332 1 2 [2, 2, 31, 43]
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
    · apply IsUnit.of_mul_eq_one (2666 : ZMod 5333)
      decide
    · apply IsUnit.of_mul_eq_one (2862 : ZMod 5333)
      decide
    · apply IsUnit.of_mul_eq_one (587 : ZMod 5333)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5347 : Nat.Prime 5347 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5347 5346 1 3 [2, 3, 3, 3, 3, 3, 11]
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
    · apply IsUnit.of_mul_eq_one (2673 : ZMod 5347)
      decide
    · apply IsUnit.of_mul_eq_one (3724 : ZMod 5347)
      decide
    · apply IsUnit.of_mul_eq_one (1863 : ZMod 5347)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5351 : Nat.Prime 5351 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5351 5350 1 11 [2, 5, 5, 107]
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
    · apply IsUnit.of_mul_eq_one (2675 : ZMod 5351)
      decide
    · apply IsUnit.of_mul_eq_one (840 : ZMod 5351)
      decide
    · apply IsUnit.of_mul_eq_one (2396 : ZMod 5351)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5381 : Nat.Prime 5381 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5381 5380 1 3 [2, 2, 5, 269]
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
    · apply IsUnit.of_mul_eq_one (2690 : ZMod 5381)
      decide
    · apply IsUnit.of_mul_eq_one (5247 : ZMod 5381)
      decide
    · apply IsUnit.of_mul_eq_one (427 : ZMod 5381)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5387 : Nat.Prime 5387 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5387 5386 1 2 [2, 2693]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (2693 : ZMod 5387)
      decide
    · apply IsUnit.of_mul_eq_one (1796 : ZMod 5387)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5393 : Nat.Prime 5393 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5393 5392 1 3 [2, 2, 2, 2, 337]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (2696 : ZMod 5393)
      decide
    · apply IsUnit.of_mul_eq_one (1021 : ZMod 5393)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5399 : Nat.Prime 5399 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5399 5398 1 7 [2, 2699]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (2699 : ZMod 5399)
      decide
    · apply IsUnit.of_mul_eq_one (2812 : ZMod 5399)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5167_5436_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5431 (p := 5309) (q := 5323) (by exact lowPrime_5323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5323) (q := 5333) (by exact lowPrime_5333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5333) (q := 5347) (by exact lowPrime_5347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5347) (q := 5351) (by exact lowPrime_5351) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5351) (q := 5381) (by exact lowPrime_5381) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5381) (q := 5387) (by exact lowPrime_5387) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5387) (q := 5393) (by exact lowPrime_5393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5431 (p := 5393) (q := 5399) (by exact lowPrime_5399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5167_5436_part03_chain :
    DusartPrimeRowsChain 5309 5398 dusartPrimeRows_5167_5436_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · norm_num [dusartPrimeRow_of_explicit_5431]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · norm_num [dusartPrimeRow_of_explicit_5431]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · norm_num [dusartPrimeRow_of_explicit_5431]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · norm_num [dusartPrimeRow_of_explicit_5431]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · norm_num [dusartPrimeRow_of_explicit_5431]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · norm_num [dusartPrimeRow_of_explicit_5431]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · norm_num [dusartPrimeRow_of_explicit_5431]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · norm_num [dusartPrimeRow_of_explicit_5431]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_5431, dusartPrimeRow_of_explicit_right]
