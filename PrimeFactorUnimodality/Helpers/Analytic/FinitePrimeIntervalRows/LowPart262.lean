import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 262 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18251 : Nat.Prime 18251 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18251 18250 1 2 [2, 5, 5, 5, 73]
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
    · apply IsUnit.of_mul_eq_one (9125 : ZMod 18251)
      decide
    · apply IsUnit.of_mul_eq_one (4597 : ZMod 18251)
      decide
    · apply IsUnit.of_mul_eq_one (2194 : ZMod 18251)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18253 : Nat.Prime 18253 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18253 18252 1 5 [2, 2, 3, 3, 3, 13, 13]
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
    · apply IsUnit.of_mul_eq_one (9126 : ZMod 18253)
      decide
    · apply IsUnit.of_mul_eq_one (9087 : ZMod 18253)
      decide
    · apply IsUnit.of_mul_eq_one (2928 : ZMod 18253)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18257 : Nat.Prime 18257 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18257 18256 1 5 [2, 2, 2, 2, 7, 163]
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
    · apply IsUnit.of_mul_eq_one (9128 : ZMod 18257)
      decide
    · apply IsUnit.of_mul_eq_one (4491 : ZMod 18257)
      decide
    · apply IsUnit.of_mul_eq_one (4217 : ZMod 18257)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18269 : Nat.Prime 18269 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18269 18268 1 2 [2, 2, 4567]
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
    · apply IsUnit.of_mul_eq_one (9134 : ZMod 18269)
      decide
    · apply IsUnit.of_mul_eq_one (1218 : ZMod 18269)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18287 : Nat.Prime 18287 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18287 18286 1 5 [2, 41, 223]
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
    · apply IsUnit.of_mul_eq_one (9143 : ZMod 18287)
      decide
    · apply IsUnit.of_mul_eq_one (10760 : ZMod 18287)
      decide
    · apply IsUnit.of_mul_eq_one (5113 : ZMod 18287)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18289 : Nat.Prime 18289 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18289 18288 1 13 [2, 2, 2, 2, 3, 3, 127]
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
    · apply IsUnit.of_mul_eq_one (9144 : ZMod 18289)
      decide
    · apply IsUnit.of_mul_eq_one (13275 : ZMod 18289)
      decide
    · apply IsUnit.of_mul_eq_one (8872 : ZMod 18289)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18301 : Nat.Prime 18301 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18301 18300 1 6 [2, 2, 3, 5, 5, 61]
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
    · apply IsUnit.of_mul_eq_one (9150 : ZMod 18301)
      decide
    · apply IsUnit.of_mul_eq_one (6530 : ZMod 18301)
      decide
    · apply IsUnit.of_mul_eq_one (11614 : ZMod 18301)
      decide
    · apply IsUnit.of_mul_eq_one (4247 : ZMod 18301)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18307 : Nat.Prime 18307 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18307 18306 1 11 [2, 3, 3, 3, 3, 113]
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
    · apply IsUnit.of_mul_eq_one (9153 : ZMod 18307)
      decide
    · apply IsUnit.of_mul_eq_one (7894 : ZMod 18307)
      decide
    · apply IsUnit.of_mul_eq_one (8525 : ZMod 18307)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18233) (q := 18251) (by exact lowPrime_18251) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18251) (q := 18253) (by exact lowPrime_18253) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18253) (q := 18257) (by exact lowPrime_18257) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18257) (q := 18269) (by exact lowPrime_18269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18269) (q := 18287) (by exact lowPrime_18287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18287) (q := 18289) (by exact lowPrime_18289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18289) (q := 18301) (by exact lowPrime_18301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18301) (q := 18307) (by exact lowPrime_18307) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part04_chain :
    DusartPrimeRowsChain 18233 18306 dusartPrimeRows_18041_18958_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18958, dusartPrimeRow_of_explicit_right]
