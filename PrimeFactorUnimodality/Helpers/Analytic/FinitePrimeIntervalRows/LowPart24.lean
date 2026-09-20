import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 24 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17939 : Nat.Prime 17939 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17939 17938 1 2 [2, 8969]
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
    · apply IsUnit.of_mul_eq_one (8969 : ZMod 17939)
      decide
    · apply IsUnit.of_mul_eq_one (5980 : ZMod 17939)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17957 : Nat.Prime 17957 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17957 17956 1 2 [2, 2, 67, 67]
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
    · apply IsUnit.of_mul_eq_one (8978 : ZMod 17957)
      decide
    · apply IsUnit.of_mul_eq_one (4269 : ZMod 17957)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17959 : Nat.Prime 17959 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17959 17958 1 6 [2, 3, 41, 73]
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
    · apply IsUnit.of_mul_eq_one (8979 : ZMod 17959)
      decide
    · apply IsUnit.of_mul_eq_one (14943 : ZMod 17959)
      decide
    · apply IsUnit.of_mul_eq_one (6642 : ZMod 17959)
      decide
    · apply IsUnit.of_mul_eq_one (4268 : ZMod 17959)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17971 : Nat.Prime 17971 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17971 17970 1 3 [2, 3, 5, 599]
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
    · apply IsUnit.of_mul_eq_one (8985 : ZMod 17971)
      decide
    · apply IsUnit.of_mul_eq_one (912 : ZMod 17971)
      decide
    · apply IsUnit.of_mul_eq_one (13702 : ZMod 17971)
      decide
    · apply IsUnit.of_mul_eq_one (1122 : ZMod 17971)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17977 : Nat.Prime 17977 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17977 17976 1 5 [2, 2, 2, 3, 7, 107]
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
    · apply IsUnit.of_mul_eq_one (8988 : ZMod 17977)
      decide
    · apply IsUnit.of_mul_eq_one (13590 : ZMod 17977)
      decide
    · apply IsUnit.of_mul_eq_one (3962 : ZMod 17977)
      decide
    · apply IsUnit.of_mul_eq_one (6547 : ZMod 17977)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17981 : Nat.Prime 17981 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17981 17980 1 2 [2, 2, 5, 29, 31]
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
    · apply IsUnit.of_mul_eq_one (8990 : ZMod 17981)
      decide
    · apply IsUnit.of_mul_eq_one (3990 : ZMod 17981)
      decide
    · apply IsUnit.of_mul_eq_one (11846 : ZMod 17981)
      decide
    · apply IsUnit.of_mul_eq_one (6443 : ZMod 17981)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17987 : Nat.Prime 17987 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17987 17986 1 5 [2, 17, 23, 23]
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
    · apply IsUnit.of_mul_eq_one (8993 : ZMod 17987)
      decide
    · apply IsUnit.of_mul_eq_one (16746 : ZMod 17987)
      decide
    · apply IsUnit.of_mul_eq_one (8008 : ZMod 17987)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_17989 : Nat.Prime 17989 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17989 17988 1 2 [2, 2, 3, 1499]
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
    · apply IsUnit.of_mul_eq_one (8994 : ZMod 17989)
      decide
    · apply IsUnit.of_mul_eq_one (15892 : ZMod 17989)
      decide
    · apply IsUnit.of_mul_eq_one (7692 : ZMod 17989)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18013 : Nat.Prime 18013 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18013 18012 1 2 [2, 2, 3, 19, 79]
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
    · apply IsUnit.of_mul_eq_one (9006 : ZMod 18013)
      decide
    · apply IsUnit.of_mul_eq_one (6780 : ZMod 18013)
      decide
    · apply IsUnit.of_mul_eq_one (8913 : ZMod 18013)
      decide
    · apply IsUnit.of_mul_eq_one (6066 : ZMod 18013)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_18041 : Nat.Prime 18041 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18041 18040 1 3 [2, 2, 2, 5, 11, 41]
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
    · apply IsUnit.of_mul_eq_one (9020 : ZMod 18041)
      decide
    · apply IsUnit.of_mul_eq_one (6345 : ZMod 18041)
      decide
    · apply IsUnit.of_mul_eq_one (8339 : ZMod 18041)
      decide
    · apply IsUnit.of_mul_eq_one (8337 : ZMod 18041)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part11 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17929) (q := 17939) (by exact lowPrime_17939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17939) (q := 17957) (by exact lowPrime_17957) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17957) (q := 17959) (by exact lowPrime_17959) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17959) (q := 17971) (by exact lowPrime_17971) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17971) (q := 17977) (by exact lowPrime_17977) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17977) (q := 17981) (by exact lowPrime_17981) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17981) (q := 17987) (by exact lowPrime_17987) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17987) (q := 17989) (by exact lowPrime_17989) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part11_chain :
    DusartPrimeRowsChain 17929 17988 dusartPrimeRows_17159_18040_part11 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]

set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17989) (q := 18013) (by exact lowPrime_18013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 18013) (q := 18041) (by exact lowPrime_18041) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part12_chain :
    DusartPrimeRowsChain 17989 18040 dusartPrimeRows_17159_18040_part12 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.empty
      norm_num [dusartPrimeRow_of_explicit_18033, dusartPrimeRow_of_explicit_right]
