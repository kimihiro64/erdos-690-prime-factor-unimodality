import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 222 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21187 : Nat.Prime 21187 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21187 21186 1 2 [2, 3, 3, 11, 107]
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
    · apply IsUnit.of_mul_eq_one (10593 : ZMod 21187)
      decide
    · apply IsUnit.of_mul_eq_one (15814 : ZMod 21187)
      decide
    · apply IsUnit.of_mul_eq_one (14840 : ZMod 21187)
      decide
    · apply IsUnit.of_mul_eq_one (12367 : ZMod 21187)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21191 : Nat.Prime 21191 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21191 21190 1 7 [2, 5, 13, 163]
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
    · apply IsUnit.of_mul_eq_one (10595 : ZMod 21191)
      decide
    · apply IsUnit.of_mul_eq_one (15486 : ZMod 21191)
      decide
    · apply IsUnit.of_mul_eq_one (20064 : ZMod 21191)
      decide
    · apply IsUnit.of_mul_eq_one (19743 : ZMod 21191)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21193 : Nat.Prime 21193 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21193 21192 1 11 [2, 2, 2, 3, 883]
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
    · apply IsUnit.of_mul_eq_one (10596 : ZMod 21193)
      decide
    · apply IsUnit.of_mul_eq_one (6349 : ZMod 21193)
      decide
    · apply IsUnit.of_mul_eq_one (12932 : ZMod 21193)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21211 : Nat.Prime 21211 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21211 21210 1 2 [2, 3, 5, 7, 101]
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
    · apply IsUnit.of_mul_eq_one (10605 : ZMod 21211)
      decide
    · apply IsUnit.of_mul_eq_one (9761 : ZMod 21211)
      decide
    · apply IsUnit.of_mul_eq_one (6205 : ZMod 21211)
      decide
    · apply IsUnit.of_mul_eq_one (391 : ZMod 21211)
      decide
    · apply IsUnit.of_mul_eq_one (19429 : ZMod 21211)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21221 : Nat.Prime 21221 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21221 21220 1 2 [2, 2, 5, 1061]
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
    · apply IsUnit.of_mul_eq_one (10610 : ZMod 21221)
      decide
    · apply IsUnit.of_mul_eq_one (2914 : ZMod 21221)
      decide
    · apply IsUnit.of_mul_eq_one (15405 : ZMod 21221)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21227 : Nat.Prime 21227 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21227 21226 1 2 [2, 10613]
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
    · apply IsUnit.of_mul_eq_one (10613 : ZMod 21227)
      decide
    · apply IsUnit.of_mul_eq_one (7076 : ZMod 21227)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21247 : Nat.Prime 21247 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21247 21246 1 3 [2, 3, 3541]
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
    · apply IsUnit.of_mul_eq_one (10623 : ZMod 21247)
      decide
    · apply IsUnit.of_mul_eq_one (10249 : ZMod 21247)
      decide
    · apply IsUnit.of_mul_eq_one (16840 : ZMod 21247)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_21269 : Nat.Prime 21269 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21269 21268 1 2 [2, 2, 13, 409]
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
    · apply IsUnit.of_mul_eq_one (10634 : ZMod 21269)
      decide
    · apply IsUnit.of_mul_eq_one (1668 : ZMod 21269)
      decide
    · apply IsUnit.of_mul_eq_one (7840 : ZMod 21269)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21179) (q := 21187) (by exact lowPrime_21187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21187) (q := 21191) (by exact lowPrime_21191) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21191) (q := 21193) (by exact lowPrime_21193) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21193) (q := 21211) (by exact lowPrime_21211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21211) (q := 21221) (by exact lowPrime_21221) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21221) (q := 21227) (by exact lowPrime_21227) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21227) (q := 21247) (by exact lowPrime_21247) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21247) (q := 21269) (by exact lowPrime_21269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part04_chain :
    DusartPrimeRowsChain 21179 21268 dusartPrimeRows_20959_22026_part04 := by
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
