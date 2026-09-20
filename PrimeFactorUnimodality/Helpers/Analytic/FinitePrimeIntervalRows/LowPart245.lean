import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 245 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20899 : Nat.Prime 20899 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20899 20898 1 2 [2, 3, 3, 3, 3, 3, 43]
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
    · apply IsUnit.of_mul_eq_one (10449 : ZMod 20899)
      decide
    · apply IsUnit.of_mul_eq_one (9762 : ZMod 20899)
      decide
    · apply IsUnit.of_mul_eq_one (17050 : ZMod 20899)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20903 : Nat.Prime 20903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20903 20902 1 5 [2, 7, 1493]
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
    · apply IsUnit.of_mul_eq_one (10451 : ZMod 20903)
      decide
    · apply IsUnit.of_mul_eq_one (2666 : ZMod 20903)
      decide
    · apply IsUnit.of_mul_eq_one (7744 : ZMod 20903)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20921 : Nat.Prime 20921 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20921 20920 1 3 [2, 2, 2, 5, 523]
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
    · apply IsUnit.of_mul_eq_one (10460 : ZMod 20921)
      decide
    · apply IsUnit.of_mul_eq_one (20657 : ZMod 20921)
      decide
    · apply IsUnit.of_mul_eq_one (13366 : ZMod 20921)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20929 : Nat.Prime 20929 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20929 20928 1 7 [2, 2, 2, 2, 2, 2, 3, 109]
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
    · apply IsUnit.of_mul_eq_one (10464 : ZMod 20929)
      decide
    · apply IsUnit.of_mul_eq_one (8981 : ZMod 20929)
      decide
    · apply IsUnit.of_mul_eq_one (12666 : ZMod 20929)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20939 : Nat.Prime 20939 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20939 20938 1 2 [2, 19, 19, 29]
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
    · apply IsUnit.of_mul_eq_one (10469 : ZMod 20939)
      decide
    · apply IsUnit.of_mul_eq_one (18401 : ZMod 20939)
      decide
    · apply IsUnit.of_mul_eq_one (14100 : ZMod 20939)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20947 : Nat.Prime 20947 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20947 20946 1 3 [2, 3, 3491]
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
    · apply IsUnit.of_mul_eq_one (10473 : ZMod 20947)
      decide
    · apply IsUnit.of_mul_eq_one (7609 : ZMod 20947)
      decide
    · apply IsUnit.of_mul_eq_one (18789 : ZMod 20947)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20959 : Nat.Prime 20959 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20959 20958 1 7 [2, 3, 7, 499]
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
    · apply IsUnit.of_mul_eq_one (10479 : ZMod 20959)
      decide
    · apply IsUnit.of_mul_eq_one (6442 : ZMod 20959)
      decide
    · apply IsUnit.of_mul_eq_one (3993 : ZMod 20959)
      decide
    · apply IsUnit.of_mul_eq_one (14799 : ZMod 20959)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20897) (q := 20899) (by exact lowPrime_20899) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20899) (q := 20903) (by exact lowPrime_20903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20903) (q := 20921) (by exact lowPrime_20921) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20921) (q := 20929) (by exact lowPrime_20929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20929) (q := 20939) (by exact lowPrime_20939) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20939) (q := 20947) (by exact lowPrime_20947) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20947) (q := 20959) (by exact lowPrime_20959) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part13_chain :
    DusartPrimeRowsChain 20897 20958 dusartPrimeRows_19937_20958_part13 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · apply DusartPrimeRowsChain.empty
                norm_num [dusartPrimeRow_of_explicit_20952, dusartPrimeRow_of_explicit_right]
