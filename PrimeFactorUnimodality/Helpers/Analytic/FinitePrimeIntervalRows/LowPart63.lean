import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 63 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7213 : Nat.Prime 7213 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7213 7212 1 5 [2, 2, 3, 601]
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
    · apply IsUnit.of_mul_eq_one (3606 : ZMod 7213)
      decide
    · apply IsUnit.of_mul_eq_one (867 : ZMod 7213)
      decide
    · apply IsUnit.of_mul_eq_one (6170 : ZMod 7213)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7219 : Nat.Prime 7219 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7219 7218 1 2 [2, 3, 3, 401]
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
    · apply IsUnit.of_mul_eq_one (3609 : ZMod 7219)
      decide
    · apply IsUnit.of_mul_eq_one (6310 : ZMod 7219)
      decide
    · apply IsUnit.of_mul_eq_one (7072 : ZMod 7219)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7229 : Nat.Prime 7229 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7229 7228 1 2 [2, 2, 13, 139]
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
    · apply IsUnit.of_mul_eq_one (3614 : ZMod 7229)
      decide
    · apply IsUnit.of_mul_eq_one (3225 : ZMod 7229)
      decide
    · apply IsUnit.of_mul_eq_one (2416 : ZMod 7229)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7237 : Nat.Prime 7237 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7237 7236 1 2 [2, 2, 3, 3, 3, 67]
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
    · apply IsUnit.of_mul_eq_one (3618 : ZMod 7237)
      decide
    · apply IsUnit.of_mul_eq_one (4214 : ZMod 7237)
      decide
    · apply IsUnit.of_mul_eq_one (1453 : ZMod 7237)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7243 : Nat.Prime 7243 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7243 7242 1 2 [2, 3, 17, 71]
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
    · apply IsUnit.of_mul_eq_one (3621 : ZMod 7243)
      decide
    · apply IsUnit.of_mul_eq_one (3686 : ZMod 7243)
      decide
    · apply IsUnit.of_mul_eq_one (1136 : ZMod 7243)
      decide
    · apply IsUnit.of_mul_eq_one (3374 : ZMod 7243)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7247 : Nat.Prime 7247 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7247 7246 1 5 [2, 3623]
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
    · apply IsUnit.of_mul_eq_one (3623 : ZMod 7247)
      decide
    · apply IsUnit.of_mul_eq_one (302 : ZMod 7247)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7253 : Nat.Prime 7253 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7253 7252 1 2 [2, 2, 7, 7, 37]
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
    · apply IsUnit.of_mul_eq_one (3626 : ZMod 7253)
      decide
    · apply IsUnit.of_mul_eq_one (3339 : ZMod 7253)
      decide
    · apply IsUnit.of_mul_eq_one (1021 : ZMod 7253)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_7283 : Nat.Prime 7283 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7283 7282 1 2 [2, 11, 331]
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
    · apply IsUnit.of_mul_eq_one (3641 : ZMod 7283)
      decide
    · apply IsUnit.of_mul_eq_one (1689 : ZMod 7283)
      decide
    · apply IsUnit.of_mul_eq_one (6064 : ZMod 7283)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7211) (q := 7213) (by exact lowPrime_7213) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7213) (q := 7219) (by exact lowPrime_7219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7219) (q := 7229) (by exact lowPrime_7229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7229) (q := 7237) (by exact lowPrime_7237) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7237) (q := 7243) (by exact lowPrime_7243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7243) (q := 7247) (by exact lowPrime_7247) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7247) (q := 7253) (by exact lowPrime_7253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7253) (q := 7283) (by exact lowPrime_7283) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part04_chain :
    DusartPrimeRowsChain 7211 7282 dusartPrimeRows_6977_7332_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_7331, dusartPrimeRow_of_explicit_right]
