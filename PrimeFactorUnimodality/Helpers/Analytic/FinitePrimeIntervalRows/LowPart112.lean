import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 112 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10499 : Nat.Prime 10499 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10499 10498 1 2 [2, 29, 181]
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
    · apply IsUnit.of_mul_eq_one (5249 : ZMod 10499)
      decide
    · apply IsUnit.of_mul_eq_one (1425 : ZMod 10499)
      decide
    · apply IsUnit.of_mul_eq_one (8138 : ZMod 10499)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10501 : Nat.Prime 10501 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10501 10500 1 2 [2, 2, 3, 5, 5, 5, 7]
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
    · apply IsUnit.of_mul_eq_one (5250 : ZMod 10501)
      decide
    · apply IsUnit.of_mul_eq_one (1923 : ZMod 10501)
      decide
    · apply IsUnit.of_mul_eq_one (1149 : ZMod 10501)
      decide
    · apply IsUnit.of_mul_eq_one (1222 : ZMod 10501)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10513 : Nat.Prime 10513 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10513 10512 1 7 [2, 2, 2, 2, 3, 3, 73]
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
    · apply IsUnit.of_mul_eq_one (5256 : ZMod 10513)
      decide
    · apply IsUnit.of_mul_eq_one (1179 : ZMod 10513)
      decide
    · apply IsUnit.of_mul_eq_one (7656 : ZMod 10513)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10529 : Nat.Prime 10529 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10529 10528 1 3 [2, 2, 2, 2, 2, 7, 47]
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
    · apply IsUnit.of_mul_eq_one (5264 : ZMod 10529)
      decide
    · apply IsUnit.of_mul_eq_one (3668 : ZMod 10529)
      decide
    · apply IsUnit.of_mul_eq_one (5177 : ZMod 10529)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10531 : Nat.Prime 10531 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10531 10530 1 3 [2, 3, 3, 3, 3, 5, 13]
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
    · apply IsUnit.of_mul_eq_one (5265 : ZMod 10531)
      decide
    · apply IsUnit.of_mul_eq_one (1693 : ZMod 10531)
      decide
    · apply IsUnit.of_mul_eq_one (142 : ZMod 10531)
      decide
    · apply IsUnit.of_mul_eq_one (5324 : ZMod 10531)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10559 : Nat.Prime 10559 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10559 10558 1 23 [2, 5279]
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
    · apply IsUnit.of_mul_eq_one (5279 : ZMod 10559)
      decide
    · apply IsUnit.of_mul_eq_one (20 : ZMod 10559)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10567 : Nat.Prime 10567 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10567 10566 1 6 [2, 3, 3, 587]
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
    · apply IsUnit.of_mul_eq_one (5283 : ZMod 10567)
      decide
    · apply IsUnit.of_mul_eq_one (6649 : ZMod 10567)
      decide
    · apply IsUnit.of_mul_eq_one (3611 : ZMod 10567)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10589 : Nat.Prime 10589 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10589 10588 1 2 [2, 2, 2647]
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
    · apply IsUnit.of_mul_eq_one (5294 : ZMod 10589)
      decide
    · apply IsUnit.of_mul_eq_one (706 : ZMod 10589)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10487) (q := 10499) (by exact lowPrime_10499) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10499) (q := 10501) (by exact lowPrime_10501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10501) (q := 10513) (by exact lowPrime_10513) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10513) (q := 10529) (by exact lowPrime_10529) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10529) (q := 10531) (by exact lowPrime_10531) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10531) (q := 10559) (by exact lowPrime_10559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10559) (q := 10567) (by exact lowPrime_10567) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10567) (q := 10589) (by exact lowPrime_10589) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part02_chain :
    DusartPrimeRowsChain 10487 10588 dusartPrimeRows_10427_10938_part02 := by
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
