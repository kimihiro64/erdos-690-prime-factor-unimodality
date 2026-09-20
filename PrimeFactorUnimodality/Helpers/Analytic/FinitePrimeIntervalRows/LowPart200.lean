import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 200 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16903 : Nat.Prime 16903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16903 16902 1 3 [2, 3, 3, 3, 313]
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
    · apply IsUnit.of_mul_eq_one (8451 : ZMod 16903)
      decide
    · apply IsUnit.of_mul_eq_one (14107 : ZMod 16903)
      decide
    · apply IsUnit.of_mul_eq_one (2649 : ZMod 16903)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16921 : Nat.Prime 16921 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16921 16920 1 17 [2, 2, 2, 3, 3, 5, 47]
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
    · apply IsUnit.of_mul_eq_one (8460 : ZMod 16921)
      decide
    · apply IsUnit.of_mul_eq_one (7089 : ZMod 16921)
      decide
    · apply IsUnit.of_mul_eq_one (3900 : ZMod 16921)
      decide
    · apply IsUnit.of_mul_eq_one (8249 : ZMod 16921)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16927 : Nat.Prime 16927 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16927 16926 1 6 [2, 3, 7, 13, 31]
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
    · apply IsUnit.of_mul_eq_one (8463 : ZMod 16927)
      decide
    · apply IsUnit.of_mul_eq_one (6575 : ZMod 16927)
      decide
    · apply IsUnit.of_mul_eq_one (9950 : ZMod 16927)
      decide
    · apply IsUnit.of_mul_eq_one (6954 : ZMod 16927)
      decide
    · apply IsUnit.of_mul_eq_one (12642 : ZMod 16927)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16931 : Nat.Prime 16931 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16931 16930 1 2 [2, 5, 1693]
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
    · apply IsUnit.of_mul_eq_one (8465 : ZMod 16931)
      decide
    · apply IsUnit.of_mul_eq_one (6655 : ZMod 16931)
      decide
    · apply IsUnit.of_mul_eq_one (14465 : ZMod 16931)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16937 : Nat.Prime 16937 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16937 16936 1 3 [2, 2, 2, 29, 73]
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
    · apply IsUnit.of_mul_eq_one (8468 : ZMod 16937)
      decide
    · apply IsUnit.of_mul_eq_one (12706 : ZMod 16937)
      decide
    · apply IsUnit.of_mul_eq_one (8118 : ZMod 16937)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16943 : Nat.Prime 16943 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16943 16942 1 5 [2, 43, 197]
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
    · apply IsUnit.of_mul_eq_one (8471 : ZMod 16943)
      decide
    · apply IsUnit.of_mul_eq_one (16517 : ZMod 16943)
      decide
    · apply IsUnit.of_mul_eq_one (13077 : ZMod 16943)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16963 : Nat.Prime 16963 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16963 16962 1 2 [2, 3, 11, 257]
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
    · apply IsUnit.of_mul_eq_one (8481 : ZMod 16963)
      decide
    · apply IsUnit.of_mul_eq_one (16347 : ZMod 16963)
      decide
    · apply IsUnit.of_mul_eq_one (10137 : ZMod 16963)
      decide
    · apply IsUnit.of_mul_eq_one (1187 : ZMod 16963)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16979 : Nat.Prime 16979 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16979 16978 1 2 [2, 13, 653]
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
    · apply IsUnit.of_mul_eq_one (8489 : ZMod 16979)
      decide
    · apply IsUnit.of_mul_eq_one (2205 : ZMod 16979)
      decide
    · apply IsUnit.of_mul_eq_one (4509 : ZMod 16979)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16901) (q := 16903) (by exact lowPrime_16903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16903) (q := 16921) (by exact lowPrime_16921) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16921) (q := 16927) (by exact lowPrime_16927) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16927) (q := 16931) (by exact lowPrime_16931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16931) (q := 16937) (by exact lowPrime_16937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16937) (q := 16943) (by exact lowPrime_16943) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16943) (q := 16963) (by exact lowPrime_16963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16963) (q := 16979) (by exact lowPrime_16979) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part08_chain :
    DusartPrimeRowsChain 16901 16978 dusartPrimeRows_16319_17158_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_17154, dusartPrimeRow_of_explicit_right]
