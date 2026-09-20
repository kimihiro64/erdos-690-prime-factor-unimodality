import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 225 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21433 : Nat.Prime 21433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21433 21432 1 5 [2, 2, 2, 3, 19, 47]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10716 : ZMod 21433)
      decide
    · apply IsUnit.of_mul_eq_one (9173 : ZMod 21433)
      decide
    · apply IsUnit.of_mul_eq_one (14244 : ZMod 21433)
      decide
    · apply IsUnit.of_mul_eq_one (19404 : ZMod 21433)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21467 : Nat.Prime 21467 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21467 21466 1 2 [2, 10733]
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
    · apply IsUnit.of_mul_eq_one (10733 : ZMod 21467)
      decide
    · apply IsUnit.of_mul_eq_one (7156 : ZMod 21467)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21481 : Nat.Prime 21481 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21481 21480 1 13 [2, 2, 2, 3, 5, 179]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10740 : ZMod 21481)
      decide
    · apply IsUnit.of_mul_eq_one (5718 : ZMod 21481)
      decide
    · apply IsUnit.of_mul_eq_one (21406 : ZMod 21481)
      decide
    · apply IsUnit.of_mul_eq_one (17671 : ZMod 21481)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21487 : Nat.Prime 21487 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21487 21486 1 3 [2, 3, 3581]
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
    · apply IsUnit.of_mul_eq_one (10743 : ZMod 21487)
      decide
    · apply IsUnit.of_mul_eq_one (11424 : ZMod 21487)
      decide
    · apply IsUnit.of_mul_eq_one (974 : ZMod 21487)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21491 : Nat.Prime 21491 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21491 21490 1 2 [2, 5, 7, 307]
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
    · apply IsUnit.of_mul_eq_one (10745 : ZMod 21491)
      decide
    · apply IsUnit.of_mul_eq_one (17394 : ZMod 21491)
      decide
    · apply IsUnit.of_mul_eq_one (2984 : ZMod 21491)
      decide
    · apply IsUnit.of_mul_eq_one (10695 : ZMod 21491)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21493 : Nat.Prime 21493 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21493 21492 1 2 [2, 2, 3, 3, 3, 199]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10746 : ZMod 21493)
      decide
    · apply IsUnit.of_mul_eq_one (6316 : ZMod 21493)
      decide
    · apply IsUnit.of_mul_eq_one (19339 : ZMod 21493)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21499 : Nat.Prime 21499 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21499 21498 1 3 [2, 3, 3583]
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
    · apply IsUnit.of_mul_eq_one (10749 : ZMod 21499)
      decide
    · apply IsUnit.of_mul_eq_one (2054 : ZMod 21499)
      decide
    · apply IsUnit.of_mul_eq_one (7944 : ZMod 21499)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21503 : Nat.Prime 21503 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21503 21502 1 5 [2, 13, 827]
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
    · apply IsUnit.of_mul_eq_one (10751 : ZMod 21503)
      decide
    · apply IsUnit.of_mul_eq_one (15718 : ZMod 21503)
      decide
    · apply IsUnit.of_mul_eq_one (15910 : ZMod 21503)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21419) (q := 21433) (by exact lowPrime_21433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21433) (q := 21467) (by exact lowPrime_21467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21467) (q := 21481) (by exact lowPrime_21481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21481) (q := 21487) (by exact lowPrime_21487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21487) (q := 21491) (by exact lowPrime_21491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21491) (q := 21493) (by exact lowPrime_21493) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21493) (q := 21499) (by exact lowPrime_21499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21499) (q := 21503) (by exact lowPrime_21503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part07_chain :
    DusartPrimeRowsChain 21419 21502 dusartPrimeRows_20959_22026_part07 := by
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
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]
