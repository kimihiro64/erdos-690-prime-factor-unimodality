import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 43 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5903 : Nat.Prime 5903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5903 5902 1 5 [2, 13, 227]
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
    · apply IsUnit.of_mul_eq_one (2951 : ZMod 5903)
      decide
    · apply IsUnit.of_mul_eq_one (4424 : ZMod 5903)
      decide
    · apply IsUnit.of_mul_eq_one (307 : ZMod 5903)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5923 : Nat.Prime 5923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5923 5922 1 2 [2, 3, 3, 7, 47]
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
    · apply IsUnit.of_mul_eq_one (2961 : ZMod 5923)
      decide
    · apply IsUnit.of_mul_eq_one (4091 : ZMod 5923)
      decide
    · apply IsUnit.of_mul_eq_one (381 : ZMod 5923)
      decide
    · apply IsUnit.of_mul_eq_one (4316 : ZMod 5923)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5927 : Nat.Prime 5927 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5927 5926 1 5 [2, 2963]
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
    · apply IsUnit.of_mul_eq_one (2963 : ZMod 5927)
      decide
    · apply IsUnit.of_mul_eq_one (247 : ZMod 5927)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5939 : Nat.Prime 5939 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5939 5938 1 2 [2, 2969]
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
    · apply IsUnit.of_mul_eq_one (2969 : ZMod 5939)
      decide
    · apply IsUnit.of_mul_eq_one (1980 : ZMod 5939)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5953 : Nat.Prime 5953 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5953 5952 1 7 [2, 2, 2, 2, 2, 2, 3, 31]
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
    · apply IsUnit.of_mul_eq_one (2976 : ZMod 5953)
      decide
    · apply IsUnit.of_mul_eq_one (4258 : ZMod 5953)
      decide
    · apply IsUnit.of_mul_eq_one (3196 : ZMod 5953)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5981 : Nat.Prime 5981 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5981 5980 1 3 [2, 2, 5, 13, 23]
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
    · apply IsUnit.of_mul_eq_one (2990 : ZMod 5981)
      decide
    · apply IsUnit.of_mul_eq_one (5804 : ZMod 5981)
      decide
    · apply IsUnit.of_mul_eq_one (3197 : ZMod 5981)
      decide
    · apply IsUnit.of_mul_eq_one (4317 : ZMod 5981)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_5987 : Nat.Prime 5987 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5987 5986 1 2 [2, 41, 73]
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
    · apply IsUnit.of_mul_eq_one (2993 : ZMod 5987)
      decide
    · apply IsUnit.of_mul_eq_one (4621 : ZMod 5987)
      decide
    · apply IsUnit.of_mul_eq_one (4878 : ZMod 5987)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6007 : Nat.Prime 6007 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6007 6006 1 3 [2, 3, 7, 11, 13]
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
    · apply IsUnit.of_mul_eq_one (3003 : ZMod 6007)
      decide
    · apply IsUnit.of_mul_eq_one (4030 : ZMod 6007)
      decide
    · apply IsUnit.of_mul_eq_one (2554 : ZMod 6007)
      decide
    · apply IsUnit.of_mul_eq_one (1704 : ZMod 6007)
      decide
    · apply IsUnit.of_mul_eq_one (931 : ZMod 6007)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_5711_6006_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6002 (p := 5897) (q := 5903) (by exact lowPrime_5903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5903) (q := 5923) (by exact lowPrime_5923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5923) (q := 5927) (by exact lowPrime_5927) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5927) (q := 5939) (by exact lowPrime_5939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5939) (q := 5953) (by exact lowPrime_5953) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5953) (q := 5981) (by exact lowPrime_5981) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5981) (q := 5987) (by exact lowPrime_5987) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6002 (p := 5987) (q := 6007) (by exact lowPrime_6007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_5711_6006_part04_chain :
    DusartPrimeRowsChain 5897 6006 dusartPrimeRows_5711_6006_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6002]
  · norm_num [dusartPrimeRow_of_explicit_6002]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6002]
    · norm_num [dusartPrimeRow_of_explicit_6002]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6002]
      · norm_num [dusartPrimeRow_of_explicit_6002]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6002]
        · norm_num [dusartPrimeRow_of_explicit_6002]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6002]
          · norm_num [dusartPrimeRow_of_explicit_6002]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6002]
            · norm_num [dusartPrimeRow_of_explicit_6002]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6002]
              · norm_num [dusartPrimeRow_of_explicit_6002]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6002]
                · norm_num [dusartPrimeRow_of_explicit_6002]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6002, dusartPrimeRow_of_explicit_right]
