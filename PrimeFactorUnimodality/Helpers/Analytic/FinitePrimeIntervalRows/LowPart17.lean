import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 17 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4271 : Nat.Prime 4271 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4271 4270 1 7 [2, 5, 7, 61]
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
    · apply IsUnit.of_mul_eq_one (2135 : ZMod 4271)
      decide
    · apply IsUnit.of_mul_eq_one (1304 : ZMod 4271)
      decide
    · apply IsUnit.of_mul_eq_one (1834 : ZMod 4271)
      decide
    · apply IsUnit.of_mul_eq_one (646 : ZMod 4271)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4273 : Nat.Prime 4273 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4273 4272 1 5 [2, 2, 2, 2, 3, 89]
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
    · apply IsUnit.of_mul_eq_one (2136 : ZMod 4273)
      decide
    · apply IsUnit.of_mul_eq_one (3385 : ZMod 4273)
      decide
    · apply IsUnit.of_mul_eq_one (184 : ZMod 4273)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4283 : Nat.Prime 4283 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4283 4282 1 2 [2, 2141]
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
    · apply IsUnit.of_mul_eq_one (2141 : ZMod 4283)
      decide
    · apply IsUnit.of_mul_eq_one (1428 : ZMod 4283)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4289 : Nat.Prime 4289 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4289 4288 1 3 [2, 2, 2, 2, 2, 2, 67]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (2144 : ZMod 4289)
      decide
    · apply IsUnit.of_mul_eq_one (836 : ZMod 4289)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4297 : Nat.Prime 4297 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4297 4296 1 5 [2, 2, 2, 3, 179]
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
    · apply IsUnit.of_mul_eq_one (2148 : ZMod 4297)
      decide
    · apply IsUnit.of_mul_eq_one (2394 : ZMod 4297)
      decide
    · apply IsUnit.of_mul_eq_one (3818 : ZMod 4297)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4327 : Nat.Prime 4327 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4327 4326 1 3 [2, 3, 7, 103]
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
    · apply IsUnit.of_mul_eq_one (2163 : ZMod 4327)
      decide
    · apply IsUnit.of_mul_eq_one (1651 : ZMod 4327)
      decide
    · apply IsUnit.of_mul_eq_one (2791 : ZMod 4327)
      decide
    · apply IsUnit.of_mul_eq_one (2422 : ZMod 4327)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4337 : Nat.Prime 4337 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4337 4336 1 3 [2, 2, 2, 2, 271]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (2168 : ZMod 4337)
      decide
    · apply IsUnit.of_mul_eq_one (4287 : ZMod 4337)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_4339 : Nat.Prime 4339 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4339 4338 1 10 [2, 3, 3, 241]
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
    · apply IsUnit.of_mul_eq_one (2169 : ZMod 4339)
      decide
    · apply IsUnit.of_mul_eq_one (2813 : ZMod 4339)
      decide
    · apply IsUnit.of_mul_eq_one (474 : ZMod 4339)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4261) (q := 4271) (by exact lowPrime_4271) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4271) (q := 4273) (by exact lowPrime_4273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4273) (q := 4283) (by exact lowPrime_4283) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4283) (q := 4289) (by exact lowPrime_4289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4289) (q := 4297) (by exact lowPrime_4297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4297) (q := 4327) (by exact lowPrime_4327) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4327) (q := 4337) (by exact lowPrime_4337) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4337) (q := 4339) (by exact lowPrime_4339) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part08_chain :
    DusartPrimeRowsChain 4261 4338 dusartPrimeRows_3803_4672_part08 := by
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
