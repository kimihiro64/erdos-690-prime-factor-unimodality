import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 14 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4079 : Nat.Prime 4079 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4079 4078 1 11 [2, 2039]
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
    · apply IsUnit.of_mul_eq_one (2039 : ZMod 4079)
      decide
    · apply IsUnit.of_mul_eq_one (34 : ZMod 4079)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4091 : Nat.Prime 4091 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4091 4090 1 2 [2, 5, 409]
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
    · apply IsUnit.of_mul_eq_one (2045 : ZMod 4091)
      decide
    · apply IsUnit.of_mul_eq_one (2319 : ZMod 4091)
      decide
    · apply IsUnit.of_mul_eq_one (4 : ZMod 4091)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4093 : Nat.Prime 4093 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4093 4092 1 2 [2, 2, 3, 11, 31]
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
    · apply IsUnit.of_mul_eq_one (2046 : ZMod 4093)
      decide
    · apply IsUnit.of_mul_eq_one (1063 : ZMod 4093)
      decide
    · apply IsUnit.of_mul_eq_one (1323 : ZMod 4093)
      decide
    · apply IsUnit.of_mul_eq_one (1877 : ZMod 4093)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4099 : Nat.Prime 4099 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4099 4098 1 2 [2, 3, 683]
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
    · apply IsUnit.of_mul_eq_one (2049 : ZMod 4099)
      decide
    · apply IsUnit.of_mul_eq_one (3426 : ZMod 4099)
      decide
    · apply IsUnit.of_mul_eq_one (3058 : ZMod 4099)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4111 : Nat.Prime 4111 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4111 4110 1 12 [2, 3, 5, 137]
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
    · apply IsUnit.of_mul_eq_one (2055 : ZMod 4111)
      decide
    · apply IsUnit.of_mul_eq_one (3092 : ZMod 4111)
      decide
    · apply IsUnit.of_mul_eq_one (2447 : ZMod 4111)
      decide
    · apply IsUnit.of_mul_eq_one (1627 : ZMod 4111)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4127 : Nat.Prime 4127 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4127 4126 1 5 [2, 2063]
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
    · apply IsUnit.of_mul_eq_one (2063 : ZMod 4127)
      decide
    · apply IsUnit.of_mul_eq_one (172 : ZMod 4127)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4129 : Nat.Prime 4129 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4129 4128 1 13 [2, 2, 2, 2, 2, 3, 43]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (2064 : ZMod 4129)
      decide
    · apply IsUnit.of_mul_eq_one (3412 : ZMod 4129)
      decide
    · apply IsUnit.of_mul_eq_one (1473 : ZMod 4129)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4133 : Nat.Prime 4133 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4133 4132 1 2 [2, 2, 1033]
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
    · apply IsUnit.of_mul_eq_one (2066 : ZMod 4133)
      decide
    · apply IsUnit.of_mul_eq_one (3582 : ZMod 4133)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4073) (q := 4079) (by exact lowPrime_4079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4079) (q := 4091) (by exact lowPrime_4091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4091) (q := 4093) (by exact lowPrime_4093) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4093) (q := 4099) (by exact lowPrime_4099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4099) (q := 4111) (by exact lowPrime_4111) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4111) (q := 4127) (by exact lowPrime_4127) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4127) (q := 4129) (by exact lowPrime_4129) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4129) (q := 4133) (by exact lowPrime_4133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part05_chain :
    DusartPrimeRowsChain 4073 4132 dusartPrimeRows_3803_4672_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · norm_num [dusartPrimeRow_of_explicit_4670]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_4670, dusartPrimeRow_of_explicit_right]
