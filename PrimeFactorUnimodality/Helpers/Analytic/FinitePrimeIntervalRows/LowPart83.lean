import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 83 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8527 : Nat.Prime 8527 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8527 8526 1 5 [2, 3, 7, 7, 29]
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
    · apply IsUnit.of_mul_eq_one (4263 : ZMod 8527)
      decide
    · apply IsUnit.of_mul_eq_one (3834 : ZMod 8527)
      decide
    · apply IsUnit.of_mul_eq_one (394 : ZMod 8527)
      decide
    · apply IsUnit.of_mul_eq_one (744 : ZMod 8527)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8537 : Nat.Prime 8537 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8537 8536 1 3 [2, 2, 2, 11, 97]
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
    · apply IsUnit.of_mul_eq_one (4268 : ZMod 8537)
      decide
    · apply IsUnit.of_mul_eq_one (544 : ZMod 8537)
      decide
    · apply IsUnit.of_mul_eq_one (7731 : ZMod 8537)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8539 : Nat.Prime 8539 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8539 8538 1 2 [2, 3, 1423]
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
    · apply IsUnit.of_mul_eq_one (4269 : ZMod 8539)
      decide
    · apply IsUnit.of_mul_eq_one (1995 : ZMod 8539)
      decide
    · apply IsUnit.of_mul_eq_one (6777 : ZMod 8539)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8543 : Nat.Prime 8543 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8543 8542 1 5 [2, 4271]
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
    · apply IsUnit.of_mul_eq_one (4271 : ZMod 8543)
      decide
    · apply IsUnit.of_mul_eq_one (356 : ZMod 8543)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8563 : Nat.Prime 8563 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8563 8562 1 2 [2, 3, 1427]
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
    · apply IsUnit.of_mul_eq_one (4281 : ZMod 8563)
      decide
    · apply IsUnit.of_mul_eq_one (4767 : ZMod 8563)
      decide
    · apply IsUnit.of_mul_eq_one (5165 : ZMod 8563)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8573 : Nat.Prime 8573 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8573 8572 1 2 [2, 2, 2143]
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
    · apply IsUnit.of_mul_eq_one (4286 : ZMod 8573)
      decide
    · apply IsUnit.of_mul_eq_one (7430 : ZMod 8573)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8581 : Nat.Prime 8581 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8581 8580 1 6 [2, 2, 3, 5, 11, 13]
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
    · apply IsUnit.of_mul_eq_one (4290 : ZMod 8581)
      decide
    · apply IsUnit.of_mul_eq_one (8439 : ZMod 8581)
      decide
    · apply IsUnit.of_mul_eq_one (8084 : ZMod 8581)
      decide
    · apply IsUnit.of_mul_eq_one (4069 : ZMod 8581)
      decide
    · apply IsUnit.of_mul_eq_one (2714 : ZMod 8581)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_8597 : Nat.Prime 8597 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8597 8596 1 2 [2, 2, 7, 307]
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
    · apply IsUnit.of_mul_eq_one (4298 : ZMod 8597)
      decide
    · apply IsUnit.of_mul_eq_one (7660 : ZMod 8597)
      decide
    · apply IsUnit.of_mul_eq_one (8411 : ZMod 8597)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8521_8962_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8955 (p := 8521) (q := 8527) (by exact lowPrime_8527) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8527) (q := 8537) (by exact lowPrime_8537) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8537) (q := 8539) (by exact lowPrime_8539) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8539) (q := 8543) (by exact lowPrime_8543) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8543) (q := 8563) (by exact lowPrime_8563) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8563) (q := 8573) (by exact lowPrime_8573) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8573) (q := 8581) (by exact lowPrime_8581) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8955 (p := 8581) (q := 8597) (by exact lowPrime_8597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8521_8962_part01_chain :
    DusartPrimeRowsChain 8521 8596 dusartPrimeRows_8521_8962_part01 := by
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
