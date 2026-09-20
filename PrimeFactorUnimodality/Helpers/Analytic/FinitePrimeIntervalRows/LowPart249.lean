import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 249 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19231 : Nat.Prime 19231 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19231 19230 1 6 [2, 3, 5, 641]
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
    · apply IsUnit.of_mul_eq_one (9615 : ZMod 19231)
      decide
    · apply IsUnit.of_mul_eq_one (15942 : ZMod 19231)
      decide
    · apply IsUnit.of_mul_eq_one (12003 : ZMod 19231)
      decide
    · apply IsUnit.of_mul_eq_one (16463 : ZMod 19231)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19237 : Nat.Prime 19237 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19237 19236 1 2 [2, 2, 3, 7, 229]
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
    · apply IsUnit.of_mul_eq_one (9618 : ZMod 19237)
      decide
    · apply IsUnit.of_mul_eq_one (12521 : ZMod 19237)
      decide
    · apply IsUnit.of_mul_eq_one (12332 : ZMod 19237)
      decide
    · apply IsUnit.of_mul_eq_one (12275 : ZMod 19237)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19249 : Nat.Prime 19249 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19249 19248 1 7 [2, 2, 2, 2, 3, 401]
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
    · apply IsUnit.of_mul_eq_one (9624 : ZMod 19249)
      decide
    · apply IsUnit.of_mul_eq_one (4130 : ZMod 19249)
      decide
    · apply IsUnit.of_mul_eq_one (15997 : ZMod 19249)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19259 : Nat.Prime 19259 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19259 19258 1 2 [2, 9629]
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
    · apply IsUnit.of_mul_eq_one (9629 : ZMod 19259)
      decide
    · apply IsUnit.of_mul_eq_one (6420 : ZMod 19259)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19267 : Nat.Prime 19267 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19267 19266 1 3 [2, 3, 13, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (9633 : ZMod 19267)
      decide
    · apply IsUnit.of_mul_eq_one (10461 : ZMod 19267)
      decide
    · apply IsUnit.of_mul_eq_one (17731 : ZMod 19267)
      decide
    · apply IsUnit.of_mul_eq_one (2619 : ZMod 19267)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19273 : Nat.Prime 19273 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19273 19272 1 5 [2, 2, 2, 3, 11, 73]
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
    · apply IsUnit.of_mul_eq_one (9636 : ZMod 19273)
      decide
    · apply IsUnit.of_mul_eq_one (13428 : ZMod 19273)
      decide
    · apply IsUnit.of_mul_eq_one (17576 : ZMod 19273)
      decide
    · apply IsUnit.of_mul_eq_one (4256 : ZMod 19273)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19289 : Nat.Prime 19289 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19289 19288 1 3 [2, 2, 2, 2411]
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
    · apply IsUnit.of_mul_eq_one (9644 : ZMod 19289)
      decide
    · apply IsUnit.of_mul_eq_one (444 : ZMod 19289)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19301 : Nat.Prime 19301 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19301 19300 1 2 [2, 2, 5, 5, 193]
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
    · apply IsUnit.of_mul_eq_one (9650 : ZMod 19301)
      decide
    · apply IsUnit.of_mul_eq_one (3175 : ZMod 19301)
      decide
    · apply IsUnit.of_mul_eq_one (17220 : ZMod 19301)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19219) (q := 19231) (by exact lowPrime_19231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19231) (q := 19237) (by exact lowPrime_19237) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19237) (q := 19249) (by exact lowPrime_19249) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19249) (q := 19259) (by exact lowPrime_19259) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19259) (q := 19267) (by exact lowPrime_19267) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19267) (q := 19273) (by exact lowPrime_19273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19273) (q := 19289) (by exact lowPrime_19289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19289) (q := 19301) (by exact lowPrime_19301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part04_chain :
    DusartPrimeRowsChain 19219 19300 dusartPrimeRows_18959_19936_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_19930, dusartPrimeRow_of_explicit_right]
