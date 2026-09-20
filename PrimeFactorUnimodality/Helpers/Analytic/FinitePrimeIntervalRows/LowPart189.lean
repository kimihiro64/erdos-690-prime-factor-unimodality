import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 189 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16067 : Nat.Prime 16067 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16067 16066 1 2 [2, 29, 277]
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
    · apply IsUnit.of_mul_eq_one (8033 : ZMod 16067)
      decide
    · apply IsUnit.of_mul_eq_one (2389 : ZMod 16067)
      decide
    · apply IsUnit.of_mul_eq_one (13292 : ZMod 16067)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16069 : Nat.Prime 16069 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16069 16068 1 2 [2, 2, 3, 13, 103]
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
    · apply IsUnit.of_mul_eq_one (8034 : ZMod 16069)
      decide
    · apply IsUnit.of_mul_eq_one (650 : ZMod 16069)
      decide
    · apply IsUnit.of_mul_eq_one (12259 : ZMod 16069)
      decide
    · apply IsUnit.of_mul_eq_one (8098 : ZMod 16069)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16073 : Nat.Prime 16073 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16073 16072 1 3 [2, 2, 2, 7, 7, 41]
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
    · apply IsUnit.of_mul_eq_one (8036 : ZMod 16073)
      decide
    · apply IsUnit.of_mul_eq_one (2262 : ZMod 16073)
      decide
    · apply IsUnit.of_mul_eq_one (4583 : ZMod 16073)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16087 : Nat.Prime 16087 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16087 16086 1 5 [2, 3, 7, 383]
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
    · apply IsUnit.of_mul_eq_one (8043 : ZMod 16087)
      decide
    · apply IsUnit.of_mul_eq_one (8851 : ZMod 16087)
      decide
    · apply IsUnit.of_mul_eq_one (3958 : ZMod 16087)
      decide
    · apply IsUnit.of_mul_eq_one (8199 : ZMod 16087)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16091 : Nat.Prime 16091 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16091 16090 1 6 [2, 5, 1609]
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
    · apply IsUnit.of_mul_eq_one (8045 : ZMod 16091)
      decide
    · apply IsUnit.of_mul_eq_one (4503 : ZMod 16091)
      decide
    · apply IsUnit.of_mul_eq_one (897 : ZMod 16091)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16097 : Nat.Prime 16097 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16097 16096 1 3 [2, 2, 2, 2, 2, 503]
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
    · apply IsUnit.of_mul_eq_one (8048 : ZMod 16097)
      decide
    · apply IsUnit.of_mul_eq_one (5528 : ZMod 16097)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16103 : Nat.Prime 16103 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16103 16102 1 5 [2, 83, 97]
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
    · apply IsUnit.of_mul_eq_one (8051 : ZMod 16103)
      decide
    · apply IsUnit.of_mul_eq_one (10766 : ZMod 16103)
      decide
    · apply IsUnit.of_mul_eq_one (2401 : ZMod 16103)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_16111 : Nat.Prime 16111 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16111 16110 1 7 [2, 3, 3, 5, 179]
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
    · apply IsUnit.of_mul_eq_one (8055 : ZMod 16111)
      decide
    · apply IsUnit.of_mul_eq_one (12629 : ZMod 16111)
      decide
    · apply IsUnit.of_mul_eq_one (1480 : ZMod 16111)
      decide
    · apply IsUnit.of_mul_eq_one (6744 : ZMod 16111)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 16063) (q := 16067) (by exact lowPrime_16067) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16067) (q := 16069) (by exact lowPrime_16069) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16069) (q := 16073) (by exact lowPrime_16073) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16073) (q := 16087) (by exact lowPrime_16087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16087) (q := 16091) (by exact lowPrime_16091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16091) (q := 16097) (by exact lowPrime_16097) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16097) (q := 16103) (by exact lowPrime_16103) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 16103) (q := 16111) (by exact lowPrime_16111) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part08_chain :
    DusartPrimeRowsChain 16063 16110 dusartPrimeRows_15527_16318_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · norm_num [dusartPrimeRow_of_explicit_16317]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · norm_num [dusartPrimeRow_of_explicit_16317]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · norm_num [dusartPrimeRow_of_explicit_16317]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · norm_num [dusartPrimeRow_of_explicit_16317]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · norm_num [dusartPrimeRow_of_explicit_16317]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · norm_num [dusartPrimeRow_of_explicit_16317]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · norm_num [dusartPrimeRow_of_explicit_16317]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · norm_num [dusartPrimeRow_of_explicit_16317]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_16317, dusartPrimeRow_of_explicit_right]
