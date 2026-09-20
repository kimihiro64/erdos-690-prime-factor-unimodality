import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 113 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10597 : Nat.Prime 10597 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10597 10596 1 5 [2, 2, 3, 883]
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
    · apply IsUnit.of_mul_eq_one (5298 : ZMod 10597)
      decide
    · apply IsUnit.of_mul_eq_one (8994 : ZMod 10597)
      decide
    · apply IsUnit.of_mul_eq_one (4434 : ZMod 10597)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10601 : Nat.Prime 10601 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10601 10600 1 3 [2, 2, 2, 5, 5, 53]
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
    · apply IsUnit.of_mul_eq_one (5300 : ZMod 10601)
      decide
    · apply IsUnit.of_mul_eq_one (6830 : ZMod 10601)
      decide
    · apply IsUnit.of_mul_eq_one (8740 : ZMod 10601)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10607 : Nat.Prime 10607 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10607 10606 1 5 [2, 5303]
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
    · apply IsUnit.of_mul_eq_one (5303 : ZMod 10607)
      decide
    · apply IsUnit.of_mul_eq_one (442 : ZMod 10607)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10613 : Nat.Prime 10613 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10613 10612 1 2 [2, 2, 7, 379]
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
    · apply IsUnit.of_mul_eq_one (5306 : ZMod 10613)
      decide
    · apply IsUnit.of_mul_eq_one (3495 : ZMod 10613)
      decide
    · apply IsUnit.of_mul_eq_one (8518 : ZMod 10613)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10627 : Nat.Prime 10627 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10627 10626 1 5 [2, 3, 7, 11, 23]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5313 : ZMod 10627)
      decide
    · apply IsUnit.of_mul_eq_one (8513 : ZMod 10627)
      decide
    · apply IsUnit.of_mul_eq_one (6544 : ZMod 10627)
      decide
    · apply IsUnit.of_mul_eq_one (407 : ZMod 10627)
      decide
    · apply IsUnit.of_mul_eq_one (8102 : ZMod 10627)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10631 : Nat.Prime 10631 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10631 10630 1 11 [2, 5, 1063]
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
    · apply IsUnit.of_mul_eq_one (5315 : ZMod 10631)
      decide
    · apply IsUnit.of_mul_eq_one (479 : ZMod 10631)
      decide
    · apply IsUnit.of_mul_eq_one (4299 : ZMod 10631)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10639 : Nat.Prime 10639 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10639 10638 1 6 [2, 3, 3, 3, 197]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5319 : ZMod 10639)
      decide
    · apply IsUnit.of_mul_eq_one (4177 : ZMod 10639)
      decide
    · apply IsUnit.of_mul_eq_one (5916 : ZMod 10639)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10651 : Nat.Prime 10651 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10651 10650 1 7 [2, 3, 5, 5, 71]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5325 : ZMod 10651)
      decide
    · apply IsUnit.of_mul_eq_one (6772 : ZMod 10651)
      decide
    · apply IsUnit.of_mul_eq_one (395 : ZMod 10651)
      decide
    · apply IsUnit.of_mul_eq_one (10055 : ZMod 10651)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10589) (q := 10597) (by exact lowPrime_10597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10597) (q := 10601) (by exact lowPrime_10601) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10601) (q := 10607) (by exact lowPrime_10607) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10607) (q := 10613) (by exact lowPrime_10613) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10613) (q := 10627) (by exact lowPrime_10627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10627) (q := 10631) (by exact lowPrime_10631) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10631) (q := 10639) (by exact lowPrime_10639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10639) (q := 10651) (by exact lowPrime_10651) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part03_chain :
    DusartPrimeRowsChain 10589 10650 dusartPrimeRows_10427_10938_part03 := by
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
                  norm_num [dusartPrimeRow_of_explicit_10938, dusartPrimeRow_of_explicit_right]
