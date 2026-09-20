import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 253 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19501 : Nat.Prime 19501 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19501 19500 1 2 [2, 2, 3, 5, 5, 5, 13]
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
    · apply IsUnit.of_mul_eq_one (9750 : ZMod 19501)
      decide
    · apply IsUnit.of_mul_eq_one (6332 : ZMod 19501)
      decide
    · apply IsUnit.of_mul_eq_one (9316 : ZMod 19501)
      decide
    · apply IsUnit.of_mul_eq_one (380 : ZMod 19501)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19507 : Nat.Prime 19507 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19507 19506 1 2 [2, 3, 3251]
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
    · apply IsUnit.of_mul_eq_one (9753 : ZMod 19507)
      decide
    · apply IsUnit.of_mul_eq_one (14280 : ZMod 19507)
      decide
    · apply IsUnit.of_mul_eq_one (3406 : ZMod 19507)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19531 : Nat.Prime 19531 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19531 19530 1 13 [2, 3, 3, 5, 7, 31]
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
    · apply IsUnit.of_mul_eq_one (9765 : ZMod 19531)
      decide
    · apply IsUnit.of_mul_eq_one (5135 : ZMod 19531)
      decide
    · apply IsUnit.of_mul_eq_one (6120 : ZMod 19531)
      decide
    · apply IsUnit.of_mul_eq_one (9922 : ZMod 19531)
      decide
    · apply IsUnit.of_mul_eq_one (95 : ZMod 19531)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19541 : Nat.Prime 19541 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19541 19540 1 2 [2, 2, 5, 977]
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
    · apply IsUnit.of_mul_eq_one (9770 : ZMod 19541)
      decide
    · apply IsUnit.of_mul_eq_one (4114 : ZMod 19541)
      decide
    · apply IsUnit.of_mul_eq_one (12421 : ZMod 19541)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19543 : Nat.Prime 19543 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19543 19542 1 3 [2, 3, 3257]
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
    · apply IsUnit.of_mul_eq_one (9771 : ZMod 19543)
      decide
    · apply IsUnit.of_mul_eq_one (2406 : ZMod 19543)
      decide
    · apply IsUnit.of_mul_eq_one (10550 : ZMod 19543)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19553 : Nat.Prime 19553 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19553 19552 1 3 [2, 2, 2, 2, 2, 13, 47]
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
    · apply IsUnit.of_mul_eq_one (9776 : ZMod 19553)
      decide
    · apply IsUnit.of_mul_eq_one (17889 : ZMod 19553)
      decide
    · apply IsUnit.of_mul_eq_one (15229 : ZMod 19553)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19559 : Nat.Prime 19559 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19559 19558 1 13 [2, 7, 11, 127]
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
    · apply IsUnit.of_mul_eq_one (9779 : ZMod 19559)
      decide
    · apply IsUnit.of_mul_eq_one (14646 : ZMod 19559)
      decide
    · apply IsUnit.of_mul_eq_one (3435 : ZMod 19559)
      decide
    · apply IsUnit.of_mul_eq_one (9643 : ZMod 19559)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19571 : Nat.Prime 19571 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19571 19570 1 2 [2, 5, 19, 103]
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
    · apply IsUnit.of_mul_eq_one (9785 : ZMod 19571)
      decide
    · apply IsUnit.of_mul_eq_one (15059 : ZMod 19571)
      decide
    · apply IsUnit.of_mul_eq_one (7401 : ZMod 19571)
      decide
    · apply IsUnit.of_mul_eq_one (359 : ZMod 19571)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19489) (q := 19501) (by exact lowPrime_19501) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19501) (q := 19507) (by exact lowPrime_19507) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19507) (q := 19531) (by exact lowPrime_19531) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19531) (q := 19541) (by exact lowPrime_19541) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19541) (q := 19543) (by exact lowPrime_19543) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19543) (q := 19553) (by exact lowPrime_19553) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19553) (q := 19559) (by exact lowPrime_19559) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19559) (q := 19571) (by exact lowPrime_19571) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part08_chain :
    DusartPrimeRowsChain 19489 19570 dusartPrimeRows_18959_19936_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]
