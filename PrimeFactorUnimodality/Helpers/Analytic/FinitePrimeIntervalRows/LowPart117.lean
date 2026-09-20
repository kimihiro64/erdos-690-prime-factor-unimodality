import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 117 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10889 : Nat.Prime 10889 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10889 10888 1 3 [2, 2, 2, 1361]
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
    · apply IsUnit.of_mul_eq_one (5444 : ZMod 10889)
      decide
    · apply IsUnit.of_mul_eq_one (8351 : ZMod 10889)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10891 : Nat.Prime 10891 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10891 10890 1 2 [2, 3, 3, 5, 11, 11]
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
    · apply IsUnit.of_mul_eq_one (5445 : ZMod 10891)
      decide
    · apply IsUnit.of_mul_eq_one (366 : ZMod 10891)
      decide
    · apply IsUnit.of_mul_eq_one (623 : ZMod 10891)
      decide
    · apply IsUnit.of_mul_eq_one (7029 : ZMod 10891)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10903 : Nat.Prime 10903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10903 10902 1 3 [2, 3, 23, 79]
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
    · apply IsUnit.of_mul_eq_one (5451 : ZMod 10903)
      decide
    · apply IsUnit.of_mul_eq_one (10743 : ZMod 10903)
      decide
    · apply IsUnit.of_mul_eq_one (680 : ZMod 10903)
      decide
    · apply IsUnit.of_mul_eq_one (3815 : ZMod 10903)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10909 : Nat.Prime 10909 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10909 10908 1 2 [2, 2, 3, 3, 3, 101]
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
    rcases hq with rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (5454 : ZMod 10909)
      decide
    · apply IsUnit.of_mul_eq_one (4183 : ZMod 10909)
      decide
    · apply IsUnit.of_mul_eq_one (10287 : ZMod 10909)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10937 : Nat.Prime 10937 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10937 10936 1 3 [2, 2, 2, 1367]
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
    · apply IsUnit.of_mul_eq_one (5468 : ZMod 10937)
      decide
    · apply IsUnit.of_mul_eq_one (8948 : ZMod 10937)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10939 : Nat.Prime 10939 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10939 10938 1 3 [2, 3, 1823]
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
    · apply IsUnit.of_mul_eq_one (5469 : ZMod 10939)
      decide
    · apply IsUnit.of_mul_eq_one (1465 : ZMod 10939)
      decide
    · apply IsUnit.of_mul_eq_one (9211 : ZMod 10939)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_10427_10938_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10938 (p := 10883) (q := 10889) (by exact lowPrime_10889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10889) (q := 10891) (by exact lowPrime_10891) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10891) (q := 10903) (by exact lowPrime_10903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10903) (q := 10909) (by exact lowPrime_10909) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10909) (q := 10937) (by exact lowPrime_10937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10938 (p := 10937) (q := 10939) (by exact lowPrime_10939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_10427_10938_part07_chain :
    DusartPrimeRowsChain 10883 10938 dusartPrimeRows_10427_10938_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · norm_num [dusartPrimeRow_of_explicit_10938]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · norm_num [dusartPrimeRow_of_explicit_10938]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · norm_num [dusartPrimeRow_of_explicit_10938]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · norm_num [dusartPrimeRow_of_explicit_10938]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · norm_num [dusartPrimeRow_of_explicit_10938]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · norm_num [dusartPrimeRow_of_explicit_10938]
            · apply DusartPrimeRowsChain.empty
              norm_num [dusartPrimeRow_of_explicit_10938, dusartPrimeRow_of_explicit_right]
