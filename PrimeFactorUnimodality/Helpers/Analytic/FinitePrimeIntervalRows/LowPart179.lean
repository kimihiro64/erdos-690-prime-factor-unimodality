import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 179 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15361 : Nat.Prime 15361 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15361 15360 1 7 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 5]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (7680 : ZMod 15361)
      decide
    · apply IsUnit.of_mul_eq_one (7809 : ZMod 15361)
      decide
    · apply IsUnit.of_mul_eq_one (11126 : ZMod 15361)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15373 : Nat.Prime 15373 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15373 15372 1 2 [2, 2, 3, 3, 7, 61]
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
    · apply IsUnit.of_mul_eq_one (7686 : ZMod 15373)
      decide
    · apply IsUnit.of_mul_eq_one (4288 : ZMod 15373)
      decide
    · apply IsUnit.of_mul_eq_one (9504 : ZMod 15373)
      decide
    · apply IsUnit.of_mul_eq_one (1067 : ZMod 15373)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15377 : Nat.Prime 15377 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15377 15376 1 3 [2, 2, 2, 2, 31, 31]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (7688 : ZMod 15377)
      decide
    · apply IsUnit.of_mul_eq_one (15168 : ZMod 15377)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15383 : Nat.Prime 15383 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15383 15382 1 5 [2, 7691]
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
    · apply IsUnit.of_mul_eq_one (7691 : ZMod 15383)
      decide
    · apply IsUnit.of_mul_eq_one (641 : ZMod 15383)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15391 : Nat.Prime 15391 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15391 15390 1 12 [2, 3, 3, 3, 3, 5, 19]
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
    · apply IsUnit.of_mul_eq_one (7695 : ZMod 15391)
      decide
    · apply IsUnit.of_mul_eq_one (6118 : ZMod 15391)
      decide
    · apply IsUnit.of_mul_eq_one (12871 : ZMod 15391)
      decide
    · apply IsUnit.of_mul_eq_one (13459 : ZMod 15391)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15401 : Nat.Prime 15401 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15401 15400 1 6 [2, 2, 2, 5, 5, 7, 11]
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
    · apply IsUnit.of_mul_eq_one (7700 : ZMod 15401)
      decide
    · apply IsUnit.of_mul_eq_one (7536 : ZMod 15401)
      decide
    · apply IsUnit.of_mul_eq_one (2703 : ZMod 15401)
      decide
    · apply IsUnit.of_mul_eq_one (394 : ZMod 15401)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15413 : Nat.Prime 15413 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15413 15412 1 2 [2, 2, 3853]
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
    · apply IsUnit.of_mul_eq_one (7706 : ZMod 15413)
      decide
    · apply IsUnit.of_mul_eq_one (13358 : ZMod 15413)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15427 : Nat.Prime 15427 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15427 15426 1 2 [2, 3, 3, 857]
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
    · apply IsUnit.of_mul_eq_one (7713 : ZMod 15427)
      decide
    · apply IsUnit.of_mul_eq_one (11363 : ZMod 15427)
      decide
    · apply IsUnit.of_mul_eq_one (15294 : ZMod 15427)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15359) (q := 15361) (by exact lowPrime_15361) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15361) (q := 15373) (by exact lowPrime_15373) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15373) (q := 15377) (by exact lowPrime_15377) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15377) (q := 15383) (by exact lowPrime_15383) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15383) (q := 15391) (by exact lowPrime_15391) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15391) (q := 15401) (by exact lowPrime_15401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15401) (q := 15413) (by exact lowPrime_15413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15413) (q := 15427) (by exact lowPrime_15427) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part09_chain :
    DusartPrimeRowsChain 15359 15426 dusartPrimeRows_14767_15526_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_15521, dusartPrimeRow_of_explicit_right]
