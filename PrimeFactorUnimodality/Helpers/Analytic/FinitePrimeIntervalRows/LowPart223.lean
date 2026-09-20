import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 223 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21277 : Nat.Prime 21277 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21277 21276 1 6 [2, 2, 3, 3, 3, 197]
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
    · apply IsUnit.of_mul_eq_one (10638 : ZMod 21277)
      decide
    · apply IsUnit.of_mul_eq_one (11411 : ZMod 21277)
      decide
    · apply IsUnit.of_mul_eq_one (17493 : ZMod 21277)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21283 : Nat.Prime 21283 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21283 21282 1 11 [2, 3, 3547]
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
    · apply IsUnit.of_mul_eq_one (10641 : ZMod 21283)
      decide
    · apply IsUnit.of_mul_eq_one (17823 : ZMod 21283)
      decide
    · apply IsUnit.of_mul_eq_one (19323 : ZMod 21283)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21313 : Nat.Prime 21313 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21313 21312 1 5 [2, 2, 2, 2, 2, 2, 3, 3, 37]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10656 : ZMod 21313)
      decide
    · apply IsUnit.of_mul_eq_one (16040 : ZMod 21313)
      decide
    · apply IsUnit.of_mul_eq_one (8113 : ZMod 21313)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21317 : Nat.Prime 21317 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21317 21316 1 2 [2, 2, 73, 73]
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
    · apply IsUnit.of_mul_eq_one (10658 : ZMod 21317)
      decide
    · apply IsUnit.of_mul_eq_one (4052 : ZMod 21317)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21319 : Nat.Prime 21319 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21319 21318 1 14 [2, 3, 11, 17, 19]
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
    · apply IsUnit.of_mul_eq_one (10659 : ZMod 21319)
      decide
    · apply IsUnit.of_mul_eq_one (17741 : ZMod 21319)
      decide
    · apply IsUnit.of_mul_eq_one (428 : ZMod 21319)
      decide
    · apply IsUnit.of_mul_eq_one (13796 : ZMod 21319)
      decide
    · apply IsUnit.of_mul_eq_one (14593 : ZMod 21319)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21323 : Nat.Prime 21323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21323 21322 1 5 [2, 7, 1523]
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
    · apply IsUnit.of_mul_eq_one (10661 : ZMod 21323)
      decide
    · apply IsUnit.of_mul_eq_one (12616 : ZMod 21323)
      decide
    · apply IsUnit.of_mul_eq_one (7854 : ZMod 21323)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21341 : Nat.Prime 21341 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21341 21340 1 2 [2, 2, 5, 11, 97]
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
    · apply IsUnit.of_mul_eq_one (10670 : ZMod 21341)
      decide
    · apply IsUnit.of_mul_eq_one (177 : ZMod 21341)
      decide
    · apply IsUnit.of_mul_eq_one (7465 : ZMod 21341)
      decide
    · apply IsUnit.of_mul_eq_one (8649 : ZMod 21341)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21347 : Nat.Prime 21347 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21347 21346 1 2 [2, 13, 821]
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
    · apply IsUnit.of_mul_eq_one (10673 : ZMod 21347)
      decide
    · apply IsUnit.of_mul_eq_one (747 : ZMod 21347)
      decide
    · apply IsUnit.of_mul_eq_one (10413 : ZMod 21347)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21269) (q := 21277) (by exact lowPrime_21277) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21277) (q := 21283) (by exact lowPrime_21283) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21283) (q := 21313) (by exact lowPrime_21313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21313) (q := 21317) (by exact lowPrime_21317) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21317) (q := 21319) (by exact lowPrime_21319) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21319) (q := 21323) (by exact lowPrime_21323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21323) (q := 21341) (by exact lowPrime_21341) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21341) (q := 21347) (by exact lowPrime_21347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part05_chain :
    DusartPrimeRowsChain 21269 21346 dusartPrimeRows_20959_22026_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_22026, dusartPrimeRow_of_explicit_right]
