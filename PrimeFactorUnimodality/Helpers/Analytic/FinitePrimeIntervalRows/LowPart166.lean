import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 166 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14489 : Nat.Prime 14489 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14489 14488 1 3 [2, 2, 2, 1811]
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
    · apply IsUnit.of_mul_eq_one (7244 : ZMod 14489)
      decide
    · apply IsUnit.of_mul_eq_one (11642 : ZMod 14489)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14503 : Nat.Prime 14503 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14503 14502 1 3 [2, 3, 2417]
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
    · apply IsUnit.of_mul_eq_one (7251 : ZMod 14503)
      decide
    · apply IsUnit.of_mul_eq_one (8277 : ZMod 14503)
      decide
    · apply IsUnit.of_mul_eq_one (5598 : ZMod 14503)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14519 : Nat.Prime 14519 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14519 14518 1 13 [2, 7, 17, 61]
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
    · apply IsUnit.of_mul_eq_one (7259 : ZMod 14519)
      decide
    · apply IsUnit.of_mul_eq_one (4315 : ZMod 14519)
      decide
    · apply IsUnit.of_mul_eq_one (7766 : ZMod 14519)
      decide
    · apply IsUnit.of_mul_eq_one (5722 : ZMod 14519)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14533 : Nat.Prime 14533 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14533 14532 1 2 [2, 2, 3, 7, 173]
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
    · apply IsUnit.of_mul_eq_one (7266 : ZMod 14533)
      decide
    · apply IsUnit.of_mul_eq_one (12302 : ZMod 14533)
      decide
    · apply IsUnit.of_mul_eq_one (9414 : ZMod 14533)
      decide
    · apply IsUnit.of_mul_eq_one (10065 : ZMod 14533)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14537 : Nat.Prime 14537 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14537 14536 1 3 [2, 2, 2, 23, 79]
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
    · apply IsUnit.of_mul_eq_one (7268 : ZMod 14537)
      decide
    · apply IsUnit.of_mul_eq_one (4092 : ZMod 14537)
      decide
    · apply IsUnit.of_mul_eq_one (2603 : ZMod 14537)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14543 : Nat.Prime 14543 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14543 14542 1 5 [2, 11, 661]
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
    · apply IsUnit.of_mul_eq_one (7271 : ZMod 14543)
      decide
    · apply IsUnit.of_mul_eq_one (527 : ZMod 14543)
      decide
    · apply IsUnit.of_mul_eq_one (9003 : ZMod 14543)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14549 : Nat.Prime 14549 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14549 14548 1 2 [2, 2, 3637]
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
    · apply IsUnit.of_mul_eq_one (7274 : ZMod 14549)
      decide
    · apply IsUnit.of_mul_eq_one (970 : ZMod 14549)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14551 : Nat.Prime 14551 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14551 14550 1 3 [2, 3, 5, 5, 97]
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
    · apply IsUnit.of_mul_eq_one (7275 : ZMod 14551)
      decide
    · apply IsUnit.of_mul_eq_one (13272 : ZMod 14551)
      decide
    · apply IsUnit.of_mul_eq_one (12157 : ZMod 14551)
      decide
    · apply IsUnit.of_mul_eq_one (4288 : ZMod 14551)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14479) (q := 14489) (by exact lowPrime_14489) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14489) (q := 14503) (by exact lowPrime_14503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14503) (q := 14519) (by exact lowPrime_14519) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14519) (q := 14533) (by exact lowPrime_14533) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14533) (q := 14537) (by exact lowPrime_14537) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14537) (q := 14543) (by exact lowPrime_14543) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14543) (q := 14549) (by exact lowPrime_14549) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14549) (q := 14551) (by exact lowPrime_14551) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part06_chain :
    DusartPrimeRowsChain 14479 14550 dusartPrimeRows_14051_14766_part06 := by
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
