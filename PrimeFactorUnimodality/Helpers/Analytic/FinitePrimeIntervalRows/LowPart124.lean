import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 124 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11423 : Nat.Prime 11423 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11423 11422 1 5 [2, 5711]
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
    · apply IsUnit.of_mul_eq_one (5711 : ZMod 11423)
      decide
    · apply IsUnit.of_mul_eq_one (476 : ZMod 11423)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11437 : Nat.Prime 11437 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11437 11436 1 2 [2, 2, 3, 953]
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
    · apply IsUnit.of_mul_eq_one (5718 : ZMod 11437)
      decide
    · apply IsUnit.of_mul_eq_one (8430 : ZMod 11437)
      decide
    · apply IsUnit.of_mul_eq_one (2603 : ZMod 11437)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11443 : Nat.Prime 11443 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11443 11442 1 2 [2, 3, 1907]
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
    · apply IsUnit.of_mul_eq_one (5721 : ZMod 11443)
      decide
    · apply IsUnit.of_mul_eq_one (4791 : ZMod 11443)
      decide
    · apply IsUnit.of_mul_eq_one (1998 : ZMod 11443)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11447 : Nat.Prime 11447 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11447 11446 1 5 [2, 59, 97]
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
    · apply IsUnit.of_mul_eq_one (5723 : ZMod 11447)
      decide
    · apply IsUnit.of_mul_eq_one (6951 : ZMod 11447)
      decide
    · apply IsUnit.of_mul_eq_one (3249 : ZMod 11447)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11467 : Nat.Prime 11467 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11467 11466 1 5 [2, 3, 3, 7, 7, 13]
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
    · apply IsUnit.of_mul_eq_one (5733 : ZMod 11467)
      decide
    · apply IsUnit.of_mul_eq_one (8778 : ZMod 11467)
      decide
    · apply IsUnit.of_mul_eq_one (530 : ZMod 11467)
      decide
    · apply IsUnit.of_mul_eq_one (9817 : ZMod 11467)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11471 : Nat.Prime 11471 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11471 11470 1 11 [2, 5, 31, 37]
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
    · apply IsUnit.of_mul_eq_one (5735 : ZMod 11471)
      decide
    · apply IsUnit.of_mul_eq_one (5662 : ZMod 11471)
      decide
    · apply IsUnit.of_mul_eq_one (7362 : ZMod 11471)
      decide
    · apply IsUnit.of_mul_eq_one (4372 : ZMod 11471)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11483 : Nat.Prime 11483 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11483 11482 1 2 [2, 5741]
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
    · apply IsUnit.of_mul_eq_one (5741 : ZMod 11483)
      decide
    · apply IsUnit.of_mul_eq_one (3828 : ZMod 11483)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11489 : Nat.Prime 11489 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11489 11488 1 3 [2, 2, 2, 2, 2, 359]
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
    · apply IsUnit.of_mul_eq_one (5744 : ZMod 11489)
      decide
    · apply IsUnit.of_mul_eq_one (1620 : ZMod 11489)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11411) (q := 11423) (by exact lowPrime_11423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11423) (q := 11437) (by exact lowPrime_11437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11437) (q := 11443) (by exact lowPrime_11443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11443) (q := 11447) (by exact lowPrime_11447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11447) (q := 11467) (by exact lowPrime_11467) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11467) (q := 11471) (by exact lowPrime_11471) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11471) (q := 11483) (by exact lowPrime_11483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11483) (q := 11489) (by exact lowPrime_11489) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part07_chain :
    DusartPrimeRowsChain 11411 11488 dusartPrimeRows_10939_11502_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]
