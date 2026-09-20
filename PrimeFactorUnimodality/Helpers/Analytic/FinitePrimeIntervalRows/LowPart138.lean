import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 138 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12401 : Nat.Prime 12401 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12401 12400 1 3 [2, 2, 2, 2, 5, 5, 31]
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
    · apply IsUnit.of_mul_eq_one (6200 : ZMod 12401)
      decide
    · apply IsUnit.of_mul_eq_one (6547 : ZMod 12401)
      decide
    · apply IsUnit.of_mul_eq_one (4992 : ZMod 12401)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12409 : Nat.Prime 12409 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12409 12408 1 7 [2, 2, 2, 3, 11, 47]
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
    · apply IsUnit.of_mul_eq_one (6204 : ZMod 12409)
      decide
    · apply IsUnit.of_mul_eq_one (5073 : ZMod 12409)
      decide
    · apply IsUnit.of_mul_eq_one (2225 : ZMod 12409)
      decide
    · apply IsUnit.of_mul_eq_one (7159 : ZMod 12409)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12413 : Nat.Prime 12413 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12413 12412 1 2 [2, 2, 29, 107]
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
    · apply IsUnit.of_mul_eq_one (6206 : ZMod 12413)
      decide
    · apply IsUnit.of_mul_eq_one (10094 : ZMod 12413)
      decide
    · apply IsUnit.of_mul_eq_one (12056 : ZMod 12413)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12421 : Nat.Prime 12421 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12421 12420 1 7 [2, 2, 3, 3, 3, 5, 23]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6210 : ZMod 12421)
      decide
    · apply IsUnit.of_mul_eq_one (6094 : ZMod 12421)
      decide
    · apply IsUnit.of_mul_eq_one (2768 : ZMod 12421)
      decide
    · apply IsUnit.of_mul_eq_one (11217 : ZMod 12421)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12433 : Nat.Prime 12433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12433 12432 1 13 [2, 2, 2, 2, 3, 7, 37]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6216 : ZMod 12433)
      decide
    · apply IsUnit.of_mul_eq_one (4181 : ZMod 12433)
      decide
    · apply IsUnit.of_mul_eq_one (1734 : ZMod 12433)
      decide
    · apply IsUnit.of_mul_eq_one (1838 : ZMod 12433)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12437 : Nat.Prime 12437 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12437 12436 1 2 [2, 2, 3109]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6218 : ZMod 12437)
      decide
    · apply IsUnit.of_mul_eq_one (5804 : ZMod 12437)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12451 : Nat.Prime 12451 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12451 12450 1 3 [2, 3, 5, 5, 83]
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
    · apply IsUnit.of_mul_eq_one (6225 : ZMod 12451)
      decide
    · apply IsUnit.of_mul_eq_one (11613 : ZMod 12451)
      decide
    · apply IsUnit.of_mul_eq_one (4657 : ZMod 12451)
      decide
    · apply IsUnit.of_mul_eq_one (10897 : ZMod 12451)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12457 : Nat.Prime 12457 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12457 12456 1 10 [2, 2, 2, 3, 3, 173]
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
    · apply IsUnit.of_mul_eq_one (6228 : ZMod 12457)
      decide
    · apply IsUnit.of_mul_eq_one (8142 : ZMod 12457)
      decide
    · apply IsUnit.of_mul_eq_one (11299 : ZMod 12457)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12391) (q := 12401) (by exact lowPrime_12401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12401) (q := 12409) (by exact lowPrime_12409) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12409) (q := 12413) (by exact lowPrime_12413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12413) (q := 12421) (by exact lowPrime_12421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12421) (q := 12433) (by exact lowPrime_12433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12433) (q := 12437) (by exact lowPrime_12437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12437) (q := 12451) (by exact lowPrime_12451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12451) (q := 12457) (by exact lowPrime_12457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part05_chain :
    DusartPrimeRowsChain 12391 12456 dusartPrimeRows_12097_12712_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · norm_num [dusartPrimeRow_of_explicit_12708]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · norm_num [dusartPrimeRow_of_explicit_12708]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · norm_num [dusartPrimeRow_of_explicit_12708]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · norm_num [dusartPrimeRow_of_explicit_12708]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · norm_num [dusartPrimeRow_of_explicit_12708]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · norm_num [dusartPrimeRow_of_explicit_12708]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · norm_num [dusartPrimeRow_of_explicit_12708]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · norm_num [dusartPrimeRow_of_explicit_12708]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_12708, dusartPrimeRow_of_explicit_right]
