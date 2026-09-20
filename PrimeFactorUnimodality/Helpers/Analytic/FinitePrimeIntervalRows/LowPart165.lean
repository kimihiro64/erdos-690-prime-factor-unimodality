import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 165 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14419 : Nat.Prime 14419 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14419 14418 1 2 [2, 3, 3, 3, 3, 89]
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
    · apply IsUnit.of_mul_eq_one (7209 : ZMod 14419)
      decide
    · apply IsUnit.of_mul_eq_one (7402 : ZMod 14419)
      decide
    · apply IsUnit.of_mul_eq_one (12556 : ZMod 14419)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14423 : Nat.Prime 14423 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14423 14422 1 5 [2, 7211]
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
    · apply IsUnit.of_mul_eq_one (7211 : ZMod 14423)
      decide
    · apply IsUnit.of_mul_eq_one (601 : ZMod 14423)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14431 : Nat.Prime 14431 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14431 14430 1 3 [2, 3, 5, 13, 37]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (7215 : ZMod 14431)
      decide
    · apply IsUnit.of_mul_eq_one (183 : ZMod 14431)
      decide
    · apply IsUnit.of_mul_eq_one (8290 : ZMod 14431)
      decide
    · apply IsUnit.of_mul_eq_one (8085 : ZMod 14431)
      decide
    · apply IsUnit.of_mul_eq_one (8644 : ZMod 14431)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14437 : Nat.Prime 14437 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14437 14436 1 5 [2, 2, 3, 3, 401]
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
    · apply IsUnit.of_mul_eq_one (7218 : ZMod 14437)
      decide
    · apply IsUnit.of_mul_eq_one (11119 : ZMod 14437)
      decide
    · apply IsUnit.of_mul_eq_one (5437 : ZMod 14437)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14447 : Nat.Prime 14447 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14447 14446 1 5 [2, 31, 233]
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
    · apply IsUnit.of_mul_eq_one (7223 : ZMod 14447)
      decide
    · apply IsUnit.of_mul_eq_one (715 : ZMod 14447)
      decide
    · apply IsUnit.of_mul_eq_one (14202 : ZMod 14447)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14449 : Nat.Prime 14449 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14449 14448 1 22 [2, 2, 2, 2, 3, 7, 43]
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
    · apply IsUnit.of_mul_eq_one (7224 : ZMod 14449)
      decide
    · apply IsUnit.of_mul_eq_one (10277 : ZMod 14449)
      decide
    · apply IsUnit.of_mul_eq_one (5335 : ZMod 14449)
      decide
    · apply IsUnit.of_mul_eq_one (2888 : ZMod 14449)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14461 : Nat.Prime 14461 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14461 14460 1 2 [2, 2, 3, 5, 241]
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
    · apply IsUnit.of_mul_eq_one (7230 : ZMod 14461)
      decide
    · apply IsUnit.of_mul_eq_one (6987 : ZMod 14461)
      decide
    · apply IsUnit.of_mul_eq_one (1223 : ZMod 14461)
      decide
    · apply IsUnit.of_mul_eq_one (985 : ZMod 14461)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14479 : Nat.Prime 14479 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14479 14478 1 3 [2, 3, 19, 127]
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
    · apply IsUnit.of_mul_eq_one (7239 : ZMod 14479)
      decide
    · apply IsUnit.of_mul_eq_one (9827 : ZMod 14479)
      decide
    · apply IsUnit.of_mul_eq_one (4435 : ZMod 14479)
      decide
    · apply IsUnit.of_mul_eq_one (8358 : ZMod 14479)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14411) (q := 14419) (by exact lowPrime_14419) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14419) (q := 14423) (by exact lowPrime_14423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14423) (q := 14431) (by exact lowPrime_14431) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14431) (q := 14437) (by exact lowPrime_14437) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14437) (q := 14447) (by exact lowPrime_14447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14447) (q := 14449) (by exact lowPrime_14449) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14449) (q := 14461) (by exact lowPrime_14461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14461) (q := 14479) (by exact lowPrime_14479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part05_chain :
    DusartPrimeRowsChain 14411 14478 dusartPrimeRows_14051_14766_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14764, dusartPrimeRow_of_explicit_right]
