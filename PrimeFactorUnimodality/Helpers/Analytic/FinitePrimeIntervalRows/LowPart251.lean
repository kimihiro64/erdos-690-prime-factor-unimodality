import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 251 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19403 : Nat.Prime 19403 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19403 19402 1 2 [2, 89, 109]
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
    · apply IsUnit.of_mul_eq_one (9701 : ZMod 19403)
      decide
    · apply IsUnit.of_mul_eq_one (15694 : ZMod 19403)
      decide
    · apply IsUnit.of_mul_eq_one (17511 : ZMod 19403)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19417 : Nat.Prime 19417 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19417 19416 1 5 [2, 2, 2, 3, 809]
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
    · apply IsUnit.of_mul_eq_one (9708 : ZMod 19417)
      decide
    · apply IsUnit.of_mul_eq_one (7956 : ZMod 19417)
      decide
    · apply IsUnit.of_mul_eq_one (11767 : ZMod 19417)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19421 : Nat.Prime 19421 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19421 19420 1 3 [2, 2, 5, 971]
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
    · apply IsUnit.of_mul_eq_one (9710 : ZMod 19421)
      decide
    · apply IsUnit.of_mul_eq_one (1289 : ZMod 19421)
      decide
    · apply IsUnit.of_mul_eq_one (15803 : ZMod 19421)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19423 : Nat.Prime 19423 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19423 19422 1 3 [2, 3, 3, 13, 83]
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
    · apply IsUnit.of_mul_eq_one (9711 : ZMod 19423)
      decide
    · apply IsUnit.of_mul_eq_one (9935 : ZMod 19423)
      decide
    · apply IsUnit.of_mul_eq_one (14481 : ZMod 19423)
      decide
    · apply IsUnit.of_mul_eq_one (4825 : ZMod 19423)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19427 : Nat.Prime 19427 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19427 19426 1 2 [2, 11, 883]
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
    · apply IsUnit.of_mul_eq_one (9713 : ZMod 19427)
      decide
    · apply IsUnit.of_mul_eq_one (17632 : ZMod 19427)
      decide
    · apply IsUnit.of_mul_eq_one (15882 : ZMod 19427)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19429 : Nat.Prime 19429 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19429 19428 1 6 [2, 2, 3, 1619]
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
    · apply IsUnit.of_mul_eq_one (9714 : ZMod 19429)
      decide
    · apply IsUnit.of_mul_eq_one (5940 : ZMod 19429)
      decide
    · apply IsUnit.of_mul_eq_one (10863 : ZMod 19429)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19433 : Nat.Prime 19433 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19433 19432 1 3 [2, 2, 2, 7, 347]
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
    · apply IsUnit.of_mul_eq_one (9716 : ZMod 19433)
      decide
    · apply IsUnit.of_mul_eq_one (7278 : ZMod 19433)
      decide
    · apply IsUnit.of_mul_eq_one (14224 : ZMod 19433)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_19441 : Nat.Prime 19441 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19441 19440 1 13 [2, 2, 2, 2, 3, 3, 3, 3, 3, 5]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (9720 : ZMod 19441)
      decide
    · apply IsUnit.of_mul_eq_one (80 : ZMod 19441)
      decide
    · apply IsUnit.of_mul_eq_one (17601 : ZMod 19441)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19391) (q := 19403) (by exact lowPrime_19403) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19403) (q := 19417) (by exact lowPrime_19417) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19417) (q := 19421) (by exact lowPrime_19421) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19421) (q := 19423) (by exact lowPrime_19423) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19423) (q := 19427) (by exact lowPrime_19427) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19427) (q := 19429) (by exact lowPrime_19429) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19429) (q := 19433) (by exact lowPrime_19433) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19433) (q := 19441) (by exact lowPrime_19441) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part06_chain :
    DusartPrimeRowsChain 19391 19440 dusartPrimeRows_18959_19936_part06 := by
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
