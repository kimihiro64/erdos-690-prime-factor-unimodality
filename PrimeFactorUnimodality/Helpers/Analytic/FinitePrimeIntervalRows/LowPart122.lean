import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 122 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11261 : Nat.Prime 11261 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11261 11260 1 2 [2, 2, 5, 563]
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
    · apply IsUnit.of_mul_eq_one (5630 : ZMod 11261)
      decide
    · apply IsUnit.of_mul_eq_one (7395 : ZMod 11261)
      decide
    · apply IsUnit.of_mul_eq_one (1306 : ZMod 11261)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11273 : Nat.Prime 11273 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11273 11272 1 3 [2, 2, 2, 1409]
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
    · apply IsUnit.of_mul_eq_one (5636 : ZMod 11273)
      decide
    · apply IsUnit.of_mul_eq_one (177 : ZMod 11273)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11279 : Nat.Prime 11279 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11279 11278 1 7 [2, 5639]
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
    · apply IsUnit.of_mul_eq_one (5639 : ZMod 11279)
      decide
    · apply IsUnit.of_mul_eq_one (235 : ZMod 11279)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11287 : Nat.Prime 11287 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11287 11286 1 3 [2, 3, 3, 3, 11, 19]
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
    · apply IsUnit.of_mul_eq_one (5643 : ZMod 11287)
      decide
    · apply IsUnit.of_mul_eq_one (6125 : ZMod 11287)
      decide
    · apply IsUnit.of_mul_eq_one (6438 : ZMod 11287)
      decide
    · apply IsUnit.of_mul_eq_one (11248 : ZMod 11287)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11299 : Nat.Prime 11299 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11299 11298 1 3 [2, 3, 7, 269]
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
    · apply IsUnit.of_mul_eq_one (5649 : ZMod 11299)
      decide
    · apply IsUnit.of_mul_eq_one (3266 : ZMod 11299)
      decide
    · apply IsUnit.of_mul_eq_one (2700 : ZMod 11299)
      decide
    · apply IsUnit.of_mul_eq_one (2206 : ZMod 11299)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11311 : Nat.Prime 11311 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11311 11310 1 3 [2, 3, 5, 13, 29]
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
    · apply IsUnit.of_mul_eq_one (5655 : ZMod 11311)
      decide
    · apply IsUnit.of_mul_eq_one (373 : ZMod 11311)
      decide
    · apply IsUnit.of_mul_eq_one (2845 : ZMod 11311)
      decide
    · apply IsUnit.of_mul_eq_one (4907 : ZMod 11311)
      decide
    · apply IsUnit.of_mul_eq_one (3474 : ZMod 11311)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11317 : Nat.Prime 11317 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11317 11316 1 2 [2, 2, 3, 23, 41]
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
    · apply IsUnit.of_mul_eq_one (5658 : ZMod 11317)
      decide
    · apply IsUnit.of_mul_eq_one (162 : ZMod 11317)
      decide
    · apply IsUnit.of_mul_eq_one (11176 : ZMod 11317)
      decide
    · apply IsUnit.of_mul_eq_one (8783 : ZMod 11317)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_11321 : Nat.Prime 11321 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11321 11320 1 3 [2, 2, 2, 5, 283]
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
    · apply IsUnit.of_mul_eq_one (5660 : ZMod 11321)
      decide
    · apply IsUnit.of_mul_eq_one (3925 : ZMod 11321)
      decide
    · apply IsUnit.of_mul_eq_one (6183 : ZMod 11321)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10939_11502_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_11498 (p := 11257) (q := 11261) (by exact lowPrime_11261) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11261) (q := 11273) (by exact lowPrime_11273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11273) (q := 11279) (by exact lowPrime_11279) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11279) (q := 11287) (by exact lowPrime_11287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11287) (q := 11299) (by exact lowPrime_11299) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11299) (q := 11311) (by exact lowPrime_11311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11311) (q := 11317) (by exact lowPrime_11317) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_11498 (p := 11317) (q := 11321) (by exact lowPrime_11321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10939_11502_part05_chain :
    DusartPrimeRowsChain 11257 11320 dusartPrimeRows_10939_11502_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · norm_num [dusartPrimeRow_of_explicit_11498]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · norm_num [dusartPrimeRow_of_explicit_11498]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · norm_num [dusartPrimeRow_of_explicit_11498]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · norm_num [dusartPrimeRow_of_explicit_11498]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · norm_num [dusartPrimeRow_of_explicit_11498]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · norm_num [dusartPrimeRow_of_explicit_11498]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · norm_num [dusartPrimeRow_of_explicit_11498]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · norm_num [dusartPrimeRow_of_explicit_11498]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_11498, dusartPrimeRow_of_explicit_right]
