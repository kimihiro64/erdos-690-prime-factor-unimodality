import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 123 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11329 : Nat.Prime 11329 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11329 11328 1 7 [2, 2, 2, 2, 2, 2, 3, 59]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5664 : ZMod 11329)
      decide
    · apply IsUnit.of_mul_eq_one (7143 : ZMod 11329)
      decide
    · apply IsUnit.of_mul_eq_one (7509 : ZMod 11329)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11351 : Nat.Prime 11351 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11351 11350 1 7 [2, 5, 5, 227]
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
    · apply IsUnit.of_mul_eq_one (5675 : ZMod 11351)
      decide
    · apply IsUnit.of_mul_eq_one (1332 : ZMod 11351)
      decide
    · apply IsUnit.of_mul_eq_one (1949 : ZMod 11351)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11353 : Nat.Prime 11353 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11353 11352 1 7 [2, 2, 2, 3, 11, 43]
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
    · apply IsUnit.of_mul_eq_one (5676 : ZMod 11353)
      decide
    · apply IsUnit.of_mul_eq_one (6799 : ZMod 11353)
      decide
    · apply IsUnit.of_mul_eq_one (6163 : ZMod 11353)
      decide
    · apply IsUnit.of_mul_eq_one (5853 : ZMod 11353)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11369 : Nat.Prime 11369 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11369 11368 1 3 [2, 2, 2, 7, 7, 29]
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
    · apply IsUnit.of_mul_eq_one (5684 : ZMod 11369)
      decide
    · apply IsUnit.of_mul_eq_one (4068 : ZMod 11369)
      decide
    · apply IsUnit.of_mul_eq_one (742 : ZMod 11369)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11383 : Nat.Prime 11383 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11383 11382 1 5 [2, 3, 7, 271]
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
    · apply IsUnit.of_mul_eq_one (5691 : ZMod 11383)
      decide
    · apply IsUnit.of_mul_eq_one (11114 : ZMod 11383)
      decide
    · apply IsUnit.of_mul_eq_one (9056 : ZMod 11383)
      decide
    · apply IsUnit.of_mul_eq_one (1210 : ZMod 11383)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11393 : Nat.Prime 11393 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11393 11392 1 3 [2, 2, 2, 2, 2, 2, 2, 89]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (5696 : ZMod 11393)
      decide
    · apply IsUnit.of_mul_eq_one (9239 : ZMod 11393)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11399 : Nat.Prime 11399 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11399 11398 1 11 [2, 41, 139]
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
    · apply IsUnit.of_mul_eq_one (5699 : ZMod 11399)
      decide
    · apply IsUnit.of_mul_eq_one (5165 : ZMod 11399)
      decide
    · apply IsUnit.of_mul_eq_one (588 : ZMod 11399)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11411 : Nat.Prime 11411 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11411 11410 1 7 [2, 5, 7, 163]
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
    · apply IsUnit.of_mul_eq_one (5705 : ZMod 11411)
      decide
    · apply IsUnit.of_mul_eq_one (3032 : ZMod 11411)
      decide
    · apply IsUnit.of_mul_eq_one (5665 : ZMod 11411)
      decide
    · apply IsUnit.of_mul_eq_one (1006 : ZMod 11411)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11321) (q := 11329) (by exact lowPrime_11329) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11329) (q := 11351) (by exact lowPrime_11351) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11351) (q := 11353) (by exact lowPrime_11353) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11353) (q := 11369) (by exact lowPrime_11369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11369) (q := 11383) (by exact lowPrime_11383) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11383) (q := 11393) (by exact lowPrime_11393) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11393) (q := 11399) (by exact lowPrime_11399) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11399) (q := 11411) (by exact lowPrime_11411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part06_chain :
    DusartPrimeRowsChain 11321 11410 dusartPrimeRows_10939_11502_part06 := by
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
