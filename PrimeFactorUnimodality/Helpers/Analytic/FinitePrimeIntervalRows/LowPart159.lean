import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 159 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13903 : Nat.Prime 13903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13903 13902 1 3 [2, 3, 7, 331]
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
    · apply IsUnit.of_mul_eq_one (6951 : ZMod 13903)
      decide
    · apply IsUnit.of_mul_eq_one (4415 : ZMod 13903)
      decide
    · apply IsUnit.of_mul_eq_one (8438 : ZMod 13903)
      decide
    · apply IsUnit.of_mul_eq_one (3786 : ZMod 13903)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13907 : Nat.Prime 13907 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13907 13906 1 2 [2, 17, 409]
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
    · apply IsUnit.of_mul_eq_one (6953 : ZMod 13907)
      decide
    · apply IsUnit.of_mul_eq_one (563 : ZMod 13907)
      decide
    · apply IsUnit.of_mul_eq_one (13516 : ZMod 13907)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13913 : Nat.Prime 13913 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13913 13912 1 3 [2, 2, 2, 37, 47]
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
    · apply IsUnit.of_mul_eq_one (6956 : ZMod 13913)
      decide
    · apply IsUnit.of_mul_eq_one (13008 : ZMod 13913)
      decide
    · apply IsUnit.of_mul_eq_one (9566 : ZMod 13913)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13921 : Nat.Prime 13921 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13921 13920 1 7 [2, 2, 2, 2, 2, 3, 5, 29]
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
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (6960 : ZMod 13921)
      decide
    · apply IsUnit.of_mul_eq_one (12931 : ZMod 13921)
      decide
    · apply IsUnit.of_mul_eq_one (6717 : ZMod 13921)
      decide
    · apply IsUnit.of_mul_eq_one (648 : ZMod 13921)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13931 : Nat.Prime 13931 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13931 13930 1 2 [2, 5, 7, 199]
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
    · apply IsUnit.of_mul_eq_one (6965 : ZMod 13931)
      decide
    · apply IsUnit.of_mul_eq_one (6123 : ZMod 13931)
      decide
    · apply IsUnit.of_mul_eq_one (4477 : ZMod 13931)
      decide
    · apply IsUnit.of_mul_eq_one (8941 : ZMod 13931)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13933 : Nat.Prime 13933 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13933 13932 1 2 [2, 2, 3, 3, 3, 3, 43]
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
    · apply IsUnit.of_mul_eq_one (6966 : ZMod 13933)
      decide
    · apply IsUnit.of_mul_eq_one (711 : ZMod 13933)
      decide
    · apply IsUnit.of_mul_eq_one (5120 : ZMod 13933)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13963 : Nat.Prime 13963 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13963 13962 1 3 [2, 3, 13, 179]
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
    · apply IsUnit.of_mul_eq_one (6981 : ZMod 13963)
      decide
    · apply IsUnit.of_mul_eq_one (180 : ZMod 13963)
      decide
    · apply IsUnit.of_mul_eq_one (1535 : ZMod 13963)
      decide
    · apply IsUnit.of_mul_eq_one (10323 : ZMod 13963)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_13967 : Nat.Prime 13967 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13967 13966 1 5 [2, 6983]
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
    · apply IsUnit.of_mul_eq_one (6983 : ZMod 13967)
      decide
    · apply IsUnit.of_mul_eq_one (582 : ZMod 13967)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13901) (q := 13903) (by exact lowPrime_13903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13903) (q := 13907) (by exact lowPrime_13907) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13907) (q := 13913) (by exact lowPrime_13913) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13913) (q := 13921) (by exact lowPrime_13921) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13921) (q := 13931) (by exact lowPrime_13931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13931) (q := 13933) (by exact lowPrime_13933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13933) (q := 13963) (by exact lowPrime_13963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13963) (q := 13967) (by exact lowPrime_13967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part08_chain :
    DusartPrimeRowsChain 13901 13966 dusartPrimeRows_13367_14050_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_14044, dusartPrimeRow_of_explicit_right]
