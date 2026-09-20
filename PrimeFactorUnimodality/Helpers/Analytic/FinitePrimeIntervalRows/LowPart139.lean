import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 139 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12473 : Nat.Prime 12473 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12473 12472 1 3 [2, 2, 2, 1559]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (6236 : ZMod 12473)
      decide
    · apply IsUnit.of_mul_eq_one (7345 : ZMod 12473)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12479 : Nat.Prime 12479 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12479 12478 1 23 [2, 17, 367]
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
    · apply IsUnit.of_mul_eq_one (6239 : ZMod 12479)
      decide
    · apply IsUnit.of_mul_eq_one (149 : ZMod 12479)
      decide
    · apply IsUnit.of_mul_eq_one (9801 : ZMod 12479)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12487 : Nat.Prime 12487 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12487 12486 1 3 [2, 3, 2081]
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
    · apply IsUnit.of_mul_eq_one (6243 : ZMod 12487)
      decide
    · apply IsUnit.of_mul_eq_one (2484 : ZMod 12487)
      decide
    · apply IsUnit.of_mul_eq_one (8662 : ZMod 12487)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12491 : Nat.Prime 12491 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12491 12490 1 2 [2, 5, 1249]
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
    · apply IsUnit.of_mul_eq_one (6245 : ZMod 12491)
      decide
    · apply IsUnit.of_mul_eq_one (9723 : ZMod 12491)
      decide
    · apply IsUnit.of_mul_eq_one (3602 : ZMod 12491)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12497 : Nat.Prime 12497 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12497 12496 1 3 [2, 2, 2, 2, 11, 71]
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
    · apply IsUnit.of_mul_eq_one (6248 : ZMod 12497)
      decide
    · apply IsUnit.of_mul_eq_one (1844 : ZMod 12497)
      decide
    · apply IsUnit.of_mul_eq_one (459 : ZMod 12497)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12503 : Nat.Prime 12503 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12503 12502 1 5 [2, 7, 19, 47]
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
    · apply IsUnit.of_mul_eq_one (6251 : ZMod 12503)
      decide
    · apply IsUnit.of_mul_eq_one (10651 : ZMod 12503)
      decide
    · apply IsUnit.of_mul_eq_one (11847 : ZMod 12503)
      decide
    · apply IsUnit.of_mul_eq_one (1457 : ZMod 12503)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12511 : Nat.Prime 12511 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12511 12510 1 3 [2, 3, 3, 5, 139]
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
    · apply IsUnit.of_mul_eq_one (6255 : ZMod 12511)
      decide
    · apply IsUnit.of_mul_eq_one (1131 : ZMod 12511)
      decide
    · apply IsUnit.of_mul_eq_one (4449 : ZMod 12511)
      decide
    · apply IsUnit.of_mul_eq_one (6900 : ZMod 12511)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_12517 : Nat.Prime 12517 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12517 12516 1 6 [2, 2, 3, 7, 149]
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
    · apply IsUnit.of_mul_eq_one (6258 : ZMod 12517)
      decide
    · apply IsUnit.of_mul_eq_one (10381 : ZMod 12517)
      decide
    · apply IsUnit.of_mul_eq_one (9433 : ZMod 12517)
      decide
    · apply IsUnit.of_mul_eq_one (10602 : ZMod 12517)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12097_12712_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12708 (p := 12457) (q := 12473) (by exact lowPrime_12473) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12473) (q := 12479) (by exact lowPrime_12479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12479) (q := 12487) (by exact lowPrime_12487) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12487) (q := 12491) (by exact lowPrime_12491) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12491) (q := 12497) (by exact lowPrime_12497) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12497) (q := 12503) (by exact lowPrime_12503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12503) (q := 12511) (by exact lowPrime_12511) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12708 (p := 12511) (q := 12517) (by exact lowPrime_12517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12097_12712_part06_chain :
    DusartPrimeRowsChain 12457 12516 dusartPrimeRows_12097_12712_part06 := by
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
