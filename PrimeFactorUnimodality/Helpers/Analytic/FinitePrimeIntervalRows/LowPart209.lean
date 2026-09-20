import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 209 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22409 : Nat.Prime 22409 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22409 22408 1 3 [2, 2, 2, 2801]
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
    · apply IsUnit.of_mul_eq_one (11204 : ZMod 22409)
      decide
    · apply IsUnit.of_mul_eq_one (13360 : ZMod 22409)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22433 : Nat.Prime 22433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22433 22432 1 3 [2, 2, 2, 2, 2, 701]
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
    · apply IsUnit.of_mul_eq_one (11216 : ZMod 22433)
      decide
    · apply IsUnit.of_mul_eq_one (14039 : ZMod 22433)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22441 : Nat.Prime 22441 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22441 22440 1 14 [2, 2, 2, 3, 5, 11, 17]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (11220 : ZMod 22441)
      decide
    · apply IsUnit.of_mul_eq_one (675 : ZMod 22441)
      decide
    · apply IsUnit.of_mul_eq_one (21885 : ZMod 22441)
      decide
    · apply IsUnit.of_mul_eq_one (4262 : ZMod 22441)
      decide
    · apply IsUnit.of_mul_eq_one (2905 : ZMod 22441)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22447 : Nat.Prime 22447 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22447 22446 1 3 [2, 3, 3, 29, 43]
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
    · apply IsUnit.of_mul_eq_one (11223 : ZMod 22447)
      decide
    · apply IsUnit.of_mul_eq_one (86 : ZMod 22447)
      decide
    · apply IsUnit.of_mul_eq_one (7450 : ZMod 22447)
      decide
    · apply IsUnit.of_mul_eq_one (4822 : ZMod 22447)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22453 : Nat.Prime 22453 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22453 22452 1 5 [2, 2, 3, 1871]
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
    · apply IsUnit.of_mul_eq_one (11226 : ZMod 22453)
      decide
    · apply IsUnit.of_mul_eq_one (8998 : ZMod 22453)
      decide
    · apply IsUnit.of_mul_eq_one (16562 : ZMod 22453)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22469 : Nat.Prime 22469 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22469 22468 1 2 [2, 2, 41, 137]
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
    · apply IsUnit.of_mul_eq_one (11234 : ZMod 22469)
      decide
    · apply IsUnit.of_mul_eq_one (140 : ZMod 22469)
      decide
    · apply IsUnit.of_mul_eq_one (17659 : ZMod 22469)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22481 : Nat.Prime 22481 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22481 22480 1 3 [2, 2, 2, 2, 5, 281]
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
    · apply IsUnit.of_mul_eq_one (11240 : ZMod 22481)
      decide
    · apply IsUnit.of_mul_eq_one (16281 : ZMod 22481)
      decide
    · apply IsUnit.of_mul_eq_one (1593 : ZMod 22481)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_22483 : Nat.Prime 22483 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22483 22482 1 2 [2, 3, 3, 1249]
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
    · apply IsUnit.of_mul_eq_one (11241 : ZMod 22483)
      decide
    · apply IsUnit.of_mul_eq_one (11482 : ZMod 22483)
      decide
    · apply IsUnit.of_mul_eq_one (9116 : ZMod 22483)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22397) (q := 22409) (by exact lowPrime_22409) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22409) (q := 22433) (by exact lowPrime_22433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22433) (q := 22441) (by exact lowPrime_22441) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22441) (q := 22447) (by exact lowPrime_22447) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22447) (q := 22453) (by exact lowPrime_22453) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22453) (q := 22469) (by exact lowPrime_22469) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22469) (q := 22481) (by exact lowPrime_22481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22481) (q := 22483) (by exact lowPrime_22483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part06_chain :
    DusartPrimeRowsChain 22397 22482 dusartPrimeRows_22027_23158_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · norm_num [dusartPrimeRow_of_explicit_23155]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · norm_num [dusartPrimeRow_of_explicit_23155]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · norm_num [dusartPrimeRow_of_explicit_23155]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_23155, dusartPrimeRow_of_explicit_right]
