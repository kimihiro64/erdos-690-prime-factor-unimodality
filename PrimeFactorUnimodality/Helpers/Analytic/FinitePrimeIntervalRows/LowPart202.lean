import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 202 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17041 : Nat.Prime 17041 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17041 17040 1 7 [2, 2, 2, 2, 3, 5, 71]
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
    · apply IsUnit.of_mul_eq_one (8520 : ZMod 17041)
      decide
    · apply IsUnit.of_mul_eq_one (6579 : ZMod 17041)
      decide
    · apply IsUnit.of_mul_eq_one (11879 : ZMod 17041)
      decide
    · apply IsUnit.of_mul_eq_one (11407 : ZMod 17041)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17047 : Nat.Prime 17047 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17047 17046 1 3 [2, 3, 3, 947]
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
    · apply IsUnit.of_mul_eq_one (8523 : ZMod 17047)
      decide
    · apply IsUnit.of_mul_eq_one (15014 : ZMod 17047)
      decide
    · apply IsUnit.of_mul_eq_one (14845 : ZMod 17047)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17053 : Nat.Prime 17053 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17053 17052 1 2 [2, 2, 3, 7, 7, 29]
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
    · apply IsUnit.of_mul_eq_one (8526 : ZMod 17053)
      decide
    · apply IsUnit.of_mul_eq_one (5799 : ZMod 17053)
      decide
    · apply IsUnit.of_mul_eq_one (2777 : ZMod 17053)
      decide
    · apply IsUnit.of_mul_eq_one (8183 : ZMod 17053)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17077 : Nat.Prime 17077 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17077 17076 1 2 [2, 2, 3, 1423]
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
    · apply IsUnit.of_mul_eq_one (8538 : ZMod 17077)
      decide
    · apply IsUnit.of_mul_eq_one (6079 : ZMod 17077)
      decide
    · apply IsUnit.of_mul_eq_one (196 : ZMod 17077)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17093 : Nat.Prime 17093 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17093 17092 1 2 [2, 2, 4273]
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
    · apply IsUnit.of_mul_eq_one (8546 : ZMod 17093)
      decide
    · apply IsUnit.of_mul_eq_one (14814 : ZMod 17093)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17099 : Nat.Prime 17099 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17099 17098 1 2 [2, 83, 103]
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
    · apply IsUnit.of_mul_eq_one (8549 : ZMod 17099)
      decide
    · apply IsUnit.of_mul_eq_one (2890 : ZMod 17099)
      decide
    · apply IsUnit.of_mul_eq_one (10337 : ZMod 17099)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17107 : Nat.Prime 17107 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17107 17106 1 3 [2, 3, 2851]
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
    · apply IsUnit.of_mul_eq_one (8553 : ZMod 17107)
      decide
    · apply IsUnit.of_mul_eq_one (13670 : ZMod 17107)
      decide
    · apply IsUnit.of_mul_eq_one (8577 : ZMod 17107)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17117 : Nat.Prime 17117 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17117 17116 1 3 [2, 2, 11, 389]
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
    · apply IsUnit.of_mul_eq_one (8558 : ZMod 17117)
      decide
    · apply IsUnit.of_mul_eq_one (10599 : ZMod 17117)
      decide
    · apply IsUnit.of_mul_eq_one (13612 : ZMod 17117)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part10 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 17033) (q := 17041) (by exact lowPrime_17041) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17041) (q := 17047) (by exact lowPrime_17047) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17047) (q := 17053) (by exact lowPrime_17053) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17053) (q := 17077) (by exact lowPrime_17077) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17077) (q := 17093) (by exact lowPrime_17093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17093) (q := 17099) (by exact lowPrime_17099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17099) (q := 17107) (by exact lowPrime_17107) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 17107) (q := 17117) (by exact lowPrime_17117) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part10_chain :
    DusartPrimeRowsChain 17033 17116 dusartPrimeRows_16319_17158_part10 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_17154, dusartPrimeRow_of_explicit_right]
