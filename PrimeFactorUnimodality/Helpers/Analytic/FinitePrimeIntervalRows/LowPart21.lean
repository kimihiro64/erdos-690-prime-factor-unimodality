import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 21 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4561 : Nat.Prime 4561 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4561 4560 1 11 [2, 2, 2, 2, 3, 5, 19]
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
    · apply IsUnit.of_mul_eq_one (2280 : ZMod 4561)
      decide
    · apply IsUnit.of_mul_eq_one (1601 : ZMod 4561)
      decide
    · apply IsUnit.of_mul_eq_one (3213 : ZMod 4561)
      decide
    · apply IsUnit.of_mul_eq_one (1941 : ZMod 4561)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4567 : Nat.Prime 4567 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4567 4566 1 3 [2, 3, 761]
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
    · apply IsUnit.of_mul_eq_one (2283 : ZMod 4567)
      decide
    · apply IsUnit.of_mul_eq_one (3415 : ZMod 4567)
      decide
    · apply IsUnit.of_mul_eq_one (1813 : ZMod 4567)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4583 : Nat.Prime 4583 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4583 4582 1 5 [2, 29, 79]
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
    · apply IsUnit.of_mul_eq_one (2291 : ZMod 4583)
      decide
    · apply IsUnit.of_mul_eq_one (3773 : ZMod 4583)
      decide
    · apply IsUnit.of_mul_eq_one (3741 : ZMod 4583)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4591 : Nat.Prime 4591 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4591 4590 1 11 [2, 3, 3, 3, 5, 17]
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
    · apply IsUnit.of_mul_eq_one (2295 : ZMod 4591)
      decide
    · apply IsUnit.of_mul_eq_one (103 : ZMod 4591)
      decide
    · apply IsUnit.of_mul_eq_one (4366 : ZMod 4591)
      decide
    · apply IsUnit.of_mul_eq_one (3885 : ZMod 4591)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4597 : Nat.Prime 4597 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4597 4596 1 5 [2, 2, 3, 383]
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
    · apply IsUnit.of_mul_eq_one (2298 : ZMod 4597)
      decide
    · apply IsUnit.of_mul_eq_one (1406 : ZMod 4597)
      decide
    · apply IsUnit.of_mul_eq_one (3696 : ZMod 4597)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4603 : Nat.Prime 4603 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4603 4602 1 2 [2, 3, 13, 59]
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
    · apply IsUnit.of_mul_eq_one (2301 : ZMod 4603)
      decide
    · apply IsUnit.of_mul_eq_one (3128 : ZMod 4603)
      decide
    · apply IsUnit.of_mul_eq_one (4174 : ZMod 4603)
      decide
    · apply IsUnit.of_mul_eq_one (4028 : ZMod 4603)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4621 : Nat.Prime 4621 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4621 4620 1 2 [2, 2, 3, 5, 7, 11]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2310 : ZMod 4621)
      decide
    · apply IsUnit.of_mul_eq_one (3668 : ZMod 4621)
      decide
    · apply IsUnit.of_mul_eq_one (1777 : ZMod 4621)
      decide
    · apply IsUnit.of_mul_eq_one (2941 : ZMod 4621)
      decide
    · apply IsUnit.of_mul_eq_one (1004 : ZMod 4621)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4637 : Nat.Prime 4637 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4637 4636 1 2 [2, 2, 19, 61]
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
    · apply IsUnit.of_mul_eq_one (2318 : ZMod 4637)
      decide
    · apply IsUnit.of_mul_eq_one (2684 : ZMod 4637)
      decide
    · apply IsUnit.of_mul_eq_one (400 : ZMod 4637)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4549) (q := 4561) (by exact lowPrime_4561) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4561) (q := 4567) (by exact lowPrime_4567) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4567) (q := 4583) (by exact lowPrime_4583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4583) (q := 4591) (by exact lowPrime_4591) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4591) (q := 4597) (by exact lowPrime_4597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4597) (q := 4603) (by exact lowPrime_4603) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4603) (q := 4621) (by exact lowPrime_4621) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4621) (q := 4637) (by exact lowPrime_4637) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part12_chain :
    DusartPrimeRowsChain 4549 4636 dusartPrimeRows_3803_4672_part12 := by
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
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]
