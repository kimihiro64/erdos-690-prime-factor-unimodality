import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 265 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18457 : Nat.Prime 18457 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18457 18456 1 5 [2, 2, 2, 3, 769]
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
    · apply IsUnit.of_mul_eq_one (9228 : ZMod 18457)
      decide
    · apply IsUnit.of_mul_eq_one (6730 : ZMod 18457)
      decide
    · apply IsUnit.of_mul_eq_one (3407 : ZMod 18457)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18461 : Nat.Prime 18461 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18461 18460 1 2 [2, 2, 5, 13, 71]
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
    · apply IsUnit.of_mul_eq_one (9230 : ZMod 18461)
      decide
    · apply IsUnit.of_mul_eq_one (9097 : ZMod 18461)
      decide
    · apply IsUnit.of_mul_eq_one (14440 : ZMod 18461)
      decide
    · apply IsUnit.of_mul_eq_one (3619 : ZMod 18461)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18481 : Nat.Prime 18481 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18481 18480 1 13 [2, 2, 2, 2, 3, 5, 7, 11]
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
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (9240 : ZMod 18481)
      decide
    · apply IsUnit.of_mul_eq_one (13751 : ZMod 18481)
      decide
    · apply IsUnit.of_mul_eq_one (3806 : ZMod 18481)
      decide
    · apply IsUnit.of_mul_eq_one (160 : ZMod 18481)
      decide
    · apply IsUnit.of_mul_eq_one (12344 : ZMod 18481)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18493 : Nat.Prime 18493 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18493 18492 1 2 [2, 2, 3, 23, 67]
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
    · apply IsUnit.of_mul_eq_one (9246 : ZMod 18493)
      decide
    · apply IsUnit.of_mul_eq_one (7381 : ZMod 18493)
      decide
    · apply IsUnit.of_mul_eq_one (3325 : ZMod 18493)
      decide
    · apply IsUnit.of_mul_eq_one (164 : ZMod 18493)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18503 : Nat.Prime 18503 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18503 18502 1 5 [2, 11, 29, 29]
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
    · apply IsUnit.of_mul_eq_one (9251 : ZMod 18503)
      decide
    · apply IsUnit.of_mul_eq_one (8656 : ZMod 18503)
      decide
    · apply IsUnit.of_mul_eq_one (18083 : ZMod 18503)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18517 : Nat.Prime 18517 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18517 18516 1 6 [2, 2, 3, 1543]
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
    · apply IsUnit.of_mul_eq_one (9258 : ZMod 18517)
      decide
    · apply IsUnit.of_mul_eq_one (1690 : ZMod 18517)
      decide
    · apply IsUnit.of_mul_eq_one (13715 : ZMod 18517)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18521 : Nat.Prime 18521 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18521 18520 1 3 [2, 2, 2, 5, 463]
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
    · apply IsUnit.of_mul_eq_one (9260 : ZMod 18521)
      decide
    · apply IsUnit.of_mul_eq_one (4206 : ZMod 18521)
      decide
    · apply IsUnit.of_mul_eq_one (315 : ZMod 18521)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18523 : Nat.Prime 18523 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18523 18522 1 3 [2, 3, 3, 3, 7, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (9261 : ZMod 18523)
      decide
    · apply IsUnit.of_mul_eq_one (1021 : ZMod 18523)
      decide
    · apply IsUnit.of_mul_eq_one (17556 : ZMod 18523)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18451) (q := 18457) (by exact lowPrime_18457) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18457) (q := 18461) (by exact lowPrime_18461) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18461) (q := 18481) (by exact lowPrime_18481) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18481) (q := 18493) (by exact lowPrime_18493) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18493) (q := 18503) (by exact lowPrime_18503) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18503) (q := 18517) (by exact lowPrime_18517) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18517) (q := 18521) (by exact lowPrime_18521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18521) (q := 18523) (by exact lowPrime_18523) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part07_chain :
    DusartPrimeRowsChain 18451 18522 dusartPrimeRows_18041_18958_part07 := by
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
