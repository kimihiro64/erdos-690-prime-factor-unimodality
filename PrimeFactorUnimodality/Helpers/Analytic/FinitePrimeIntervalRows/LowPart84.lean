import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 84 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8599 : Nat.Prime 8599 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8599 8598 1 3 [2, 3, 1433]
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
    · apply IsUnit.of_mul_eq_one (4299 : ZMod 8599)
      decide
    · apply IsUnit.of_mul_eq_one (6134 : ZMod 8599)
      decide
    · apply IsUnit.of_mul_eq_one (5398 : ZMod 8599)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8609 : Nat.Prime 8609 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8609 8608 1 3 [2, 2, 2, 2, 2, 269]
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
    · apply IsUnit.of_mul_eq_one (4304 : ZMod 8609)
      decide
    · apply IsUnit.of_mul_eq_one (4780 : ZMod 8609)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8623 : Nat.Prime 8623 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8623 8622 1 3 [2, 3, 3, 479]
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
    · apply IsUnit.of_mul_eq_one (4311 : ZMod 8623)
      decide
    · apply IsUnit.of_mul_eq_one (5233 : ZMod 8623)
      decide
    · apply IsUnit.of_mul_eq_one (4775 : ZMod 8623)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8627 : Nat.Prime 8627 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8627 8626 1 2 [2, 19, 227]
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
    · apply IsUnit.of_mul_eq_one (4313 : ZMod 8627)
      decide
    · apply IsUnit.of_mul_eq_one (482 : ZMod 8627)
      decide
    · apply IsUnit.of_mul_eq_one (3929 : ZMod 8627)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8629 : Nat.Prime 8629 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8629 8628 1 6 [2, 2, 3, 719]
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
    · apply IsUnit.of_mul_eq_one (4314 : ZMod 8629)
      decide
    · apply IsUnit.of_mul_eq_one (4650 : ZMod 8629)
      decide
    · apply IsUnit.of_mul_eq_one (2319 : ZMod 8629)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8641 : Nat.Prime 8641 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8641 8640 1 17 [2, 2, 2, 2, 2, 2, 3, 3, 3, 5]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (4320 : ZMod 8641)
      decide
    · apply IsUnit.of_mul_eq_one (6951 : ZMod 8641)
      decide
    · apply IsUnit.of_mul_eq_one (3801 : ZMod 8641)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8647 : Nat.Prime 8647 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8647 8646 1 3 [2, 3, 11, 131]
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
    · apply IsUnit.of_mul_eq_one (4323 : ZMod 8647)
      decide
    · apply IsUnit.of_mul_eq_one (2617 : ZMod 8647)
      decide
    · apply IsUnit.of_mul_eq_one (6748 : ZMod 8647)
      decide
    · apply IsUnit.of_mul_eq_one (2137 : ZMod 8647)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8663 : Nat.Prime 8663 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8663 8662 1 5 [2, 61, 71]
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
    · apply IsUnit.of_mul_eq_one (4331 : ZMod 8663)
      decide
    · apply IsUnit.of_mul_eq_one (4990 : ZMod 8663)
      decide
    · apply IsUnit.of_mul_eq_one (6368 : ZMod 8663)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8597) (q := 8599) (by exact lowPrime_8599) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8599) (q := 8609) (by exact lowPrime_8609) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8609) (q := 8623) (by exact lowPrime_8623) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8623) (q := 8627) (by exact lowPrime_8627) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8627) (q := 8629) (by exact lowPrime_8629) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8629) (q := 8641) (by exact lowPrime_8641) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8641) (q := 8647) (by exact lowPrime_8647) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8647) (q := 8663) (by exact lowPrime_8663) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part02_chain :
    DusartPrimeRowsChain 8597 8662 dusartPrimeRows_8521_8962_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · norm_num [dusartPrimeRow_of_explicit_8955]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · norm_num [dusartPrimeRow_of_explicit_8955]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · norm_num [dusartPrimeRow_of_explicit_8955]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · norm_num [dusartPrimeRow_of_explicit_8955]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · norm_num [dusartPrimeRow_of_explicit_8955]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · norm_num [dusartPrimeRow_of_explicit_8955]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · norm_num [dusartPrimeRow_of_explicit_8955]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · norm_num [dusartPrimeRow_of_explicit_8955]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_8955, dusartPrimeRow_of_explicit_right]
