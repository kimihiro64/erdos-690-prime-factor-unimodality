import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 264 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18397 : Nat.Prime 18397 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18397 18396 1 6 [2, 2, 3, 3, 7, 73]
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
    · apply IsUnit.of_mul_eq_one (9198 : ZMod 18397)
      decide
    · apply IsUnit.of_mul_eq_one (882 : ZMod 18397)
      decide
    · apply IsUnit.of_mul_eq_one (2579 : ZMod 18397)
      decide
    · apply IsUnit.of_mul_eq_one (125 : ZMod 18397)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18401 : Nat.Prime 18401 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18401 18400 1 3 [2, 2, 2, 2, 2, 5, 5, 23]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (9200 : ZMod 18401)
      decide
    · apply IsUnit.of_mul_eq_one (818 : ZMod 18401)
      decide
    · apply IsUnit.of_mul_eq_one (6221 : ZMod 18401)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18413 : Nat.Prime 18413 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18413 18412 1 2 [2, 2, 4603]
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
    · apply IsUnit.of_mul_eq_one (9206 : ZMod 18413)
      decide
    · apply IsUnit.of_mul_eq_one (15958 : ZMod 18413)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18427 : Nat.Prime 18427 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18427 18426 1 2 [2, 3, 37, 83]
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
    · apply IsUnit.of_mul_eq_one (9213 : ZMod 18427)
      decide
    · apply IsUnit.of_mul_eq_one (5620 : ZMod 18427)
      decide
    · apply IsUnit.of_mul_eq_one (17644 : ZMod 18427)
      decide
    · apply IsUnit.of_mul_eq_one (6299 : ZMod 18427)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18433 : Nat.Prime 18433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18433 18432 1 5 [2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (9216 : ZMod 18433)
      decide
    · apply IsUnit.of_mul_eq_one (1261 : ZMod 18433)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18439 : Nat.Prime 18439 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18439 18438 1 3 [2, 3, 7, 439]
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
    · apply IsUnit.of_mul_eq_one (9219 : ZMod 18439)
      decide
    · apply IsUnit.of_mul_eq_one (15742 : ZMod 18439)
      decide
    · apply IsUnit.of_mul_eq_one (10852 : ZMod 18439)
      decide
    · apply IsUnit.of_mul_eq_one (11356 : ZMod 18439)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18443 : Nat.Prime 18443 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18443 18442 1 2 [2, 9221]
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
    · apply IsUnit.of_mul_eq_one (9221 : ZMod 18443)
      decide
    · apply IsUnit.of_mul_eq_one (6148 : ZMod 18443)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18451 : Nat.Prime 18451 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18451 18450 1 3 [2, 3, 3, 5, 5, 41]
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
    · apply IsUnit.of_mul_eq_one (9225 : ZMod 18451)
      decide
    · apply IsUnit.of_mul_eq_one (2791 : ZMod 18451)
      decide
    · apply IsUnit.of_mul_eq_one (1554 : ZMod 18451)
      decide
    · apply IsUnit.of_mul_eq_one (10309 : ZMod 18451)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18379) (q := 18397) (by exact lowPrime_18397) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18397) (q := 18401) (by exact lowPrime_18401) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18401) (q := 18413) (by exact lowPrime_18413) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18413) (q := 18427) (by exact lowPrime_18427) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18427) (q := 18433) (by exact lowPrime_18433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18433) (q := 18439) (by exact lowPrime_18439) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18439) (q := 18443) (by exact lowPrime_18443) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18443) (q := 18451) (by exact lowPrime_18451) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part06_chain :
    DusartPrimeRowsChain 18379 18450 dusartPrimeRows_18041_18958_part06 := by
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
