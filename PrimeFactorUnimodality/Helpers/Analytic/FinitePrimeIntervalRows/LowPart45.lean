import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 45 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6079 : Nat.Prime 6079 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6079 6078 1 17 [2, 3, 1013]
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
    · apply IsUnit.of_mul_eq_one (3039 : ZMod 6079)
      decide
    · apply IsUnit.of_mul_eq_one (1508 : ZMod 6079)
      decide
    · apply IsUnit.of_mul_eq_one (4895 : ZMod 6079)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6089 : Nat.Prime 6089 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6089 6088 1 3 [2, 2, 2, 761]
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
    · apply IsUnit.of_mul_eq_one (3044 : ZMod 6089)
      decide
    · apply IsUnit.of_mul_eq_one (1254 : ZMod 6089)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6091 : Nat.Prime 6091 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6091 6090 1 7 [2, 3, 5, 7, 29]
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
    · apply IsUnit.of_mul_eq_one (3045 : ZMod 6091)
      decide
    · apply IsUnit.of_mul_eq_one (2278 : ZMod 6091)
      decide
    · apply IsUnit.of_mul_eq_one (1836 : ZMod 6091)
      decide
    · apply IsUnit.of_mul_eq_one (1226 : ZMod 6091)
      decide
    · apply IsUnit.of_mul_eq_one (3205 : ZMod 6091)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6101 : Nat.Prime 6101 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6101 6100 1 2 [2, 2, 5, 5, 61]
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
    · apply IsUnit.of_mul_eq_one (3050 : ZMod 6101)
      decide
    · apply IsUnit.of_mul_eq_one (3503 : ZMod 6101)
      decide
    · apply IsUnit.of_mul_eq_one (4968 : ZMod 6101)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6113 : Nat.Prime 6113 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6113 6112 1 3 [2, 2, 2, 2, 2, 191]
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
    · apply IsUnit.of_mul_eq_one (3056 : ZMod 6113)
      decide
    · apply IsUnit.of_mul_eq_one (399 : ZMod 6113)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6121 : Nat.Prime 6121 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6121 6120 1 7 [2, 2, 2, 3, 3, 5, 17]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (3060 : ZMod 6121)
      decide
    · apply IsUnit.of_mul_eq_one (2424 : ZMod 6121)
      decide
    · apply IsUnit.of_mul_eq_one (4649 : ZMod 6121)
      decide
    · apply IsUnit.of_mul_eq_one (1797 : ZMod 6121)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6131 : Nat.Prime 6131 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6131 6130 1 2 [2, 5, 613]
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
    · apply IsUnit.of_mul_eq_one (3065 : ZMod 6131)
      decide
    · apply IsUnit.of_mul_eq_one (4906 : ZMod 6131)
      decide
    · apply IsUnit.of_mul_eq_one (5256 : ZMod 6131)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6133 : Nat.Prime 6133 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6133 6132 1 5 [2, 2, 3, 7, 73]
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
    · apply IsUnit.of_mul_eq_one (3066 : ZMod 6133)
      decide
    · apply IsUnit.of_mul_eq_one (316 : ZMod 6133)
      decide
    · apply IsUnit.of_mul_eq_one (443 : ZMod 6133)
      decide
    · apply IsUnit.of_mul_eq_one (5878 : ZMod 6133)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6073) (q := 6079) (by exact lowPrime_6079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6079) (q := 6089) (by exact lowPrime_6089) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6089) (q := 6091) (by exact lowPrime_6091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6091) (q := 6101) (by exact lowPrime_6101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6101) (q := 6113) (by exact lowPrime_6113) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6113) (q := 6121) (by exact lowPrime_6121) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6121) (q := 6131) (by exact lowPrime_6131) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6131) (q := 6133) (by exact lowPrime_6133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part02_chain :
    DusartPrimeRowsChain 6073 6132 dusartPrimeRows_6007_6310_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6310, dusartPrimeRow_of_explicit_right]
