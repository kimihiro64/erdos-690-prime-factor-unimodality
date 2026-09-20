import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 164 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14341 : Nat.Prime 14341 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14341 14340 1 2 [2, 2, 3, 5, 239]
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
    · apply IsUnit.of_mul_eq_one (7170 : ZMod 14341)
      decide
    · apply IsUnit.of_mul_eq_one (7440 : ZMod 14341)
      decide
    · apply IsUnit.of_mul_eq_one (4814 : ZMod 14341)
      decide
    · apply IsUnit.of_mul_eq_one (8442 : ZMod 14341)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14347 : Nat.Prime 14347 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14347 14346 1 3 [2, 3, 3, 797]
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
    · apply IsUnit.of_mul_eq_one (7173 : ZMod 14347)
      decide
    · apply IsUnit.of_mul_eq_one (8074 : ZMod 14347)
      decide
    · apply IsUnit.of_mul_eq_one (445 : ZMod 14347)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14369 : Nat.Prime 14369 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14369 14368 1 3 [2, 2, 2, 2, 2, 449]
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
    · apply IsUnit.of_mul_eq_one (7184 : ZMod 14369)
      decide
    · apply IsUnit.of_mul_eq_one (11784 : ZMod 14369)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14387 : Nat.Prime 14387 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14387 14386 1 2 [2, 7193]
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
    · apply IsUnit.of_mul_eq_one (7193 : ZMod 14387)
      decide
    · apply IsUnit.of_mul_eq_one (4796 : ZMod 14387)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14389 : Nat.Prime 14389 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14389 14388 1 2 [2, 2, 3, 11, 109]
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
    · apply IsUnit.of_mul_eq_one (7194 : ZMod 14389)
      decide
    · apply IsUnit.of_mul_eq_one (4940 : ZMod 14389)
      decide
    · apply IsUnit.of_mul_eq_one (10589 : ZMod 14389)
      decide
    · apply IsUnit.of_mul_eq_one (11347 : ZMod 14389)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14401 : Nat.Prime 14401 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14401 14400 1 11 [2, 2, 2, 2, 2, 2, 3, 3, 5, 5]
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
    · apply IsUnit.of_mul_eq_one (7200 : ZMod 14401)
      decide
    · apply IsUnit.of_mul_eq_one (4694 : ZMod 14401)
      decide
    · apply IsUnit.of_mul_eq_one (1139 : ZMod 14401)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14407 : Nat.Prime 14407 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14407 14406 1 19 [2, 3, 7, 7, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (7203 : ZMod 14407)
      decide
    · apply IsUnit.of_mul_eq_one (5907 : ZMod 14407)
      decide
    · apply IsUnit.of_mul_eq_one (8040 : ZMod 14407)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_14411 : Nat.Prime 14411 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14411 14410 1 2 [2, 5, 11, 131]
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
    · apply IsUnit.of_mul_eq_one (7205 : ZMod 14411)
      decide
    · apply IsUnit.of_mul_eq_one (10844 : ZMod 14411)
      decide
    · apply IsUnit.of_mul_eq_one (5190 : ZMod 14411)
      decide
    · apply IsUnit.of_mul_eq_one (7605 : ZMod 14411)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14327) (q := 14341) (by exact lowPrime_14341) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14341) (q := 14347) (by exact lowPrime_14347) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14347) (q := 14369) (by exact lowPrime_14369) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14369) (q := 14387) (by exact lowPrime_14387) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14387) (q := 14389) (by exact lowPrime_14389) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14389) (q := 14401) (by exact lowPrime_14401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14401) (q := 14407) (by exact lowPrime_14407) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14407) (q := 14411) (by exact lowPrime_14411) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part04_chain :
    DusartPrimeRowsChain 14327 14410 dusartPrimeRows_14051_14766_part04 := by
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
