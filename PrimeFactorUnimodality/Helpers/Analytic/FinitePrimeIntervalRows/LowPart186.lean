import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 186 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15809 : Nat.Prime 15809 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15809 15808 1 3 [2, 2, 2, 2, 2, 2, 13, 19]
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
    · apply IsUnit.of_mul_eq_one (7904 : ZMod 15809)
      decide
    · apply IsUnit.of_mul_eq_one (4754 : ZMod 15809)
      decide
    · apply IsUnit.of_mul_eq_one (10322 : ZMod 15809)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15817 : Nat.Prime 15817 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15817 15816 1 5 [2, 2, 2, 3, 659]
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
    · apply IsUnit.of_mul_eq_one (7908 : ZMod 15817)
      decide
    · apply IsUnit.of_mul_eq_one (9553 : ZMod 15817)
      decide
    · apply IsUnit.of_mul_eq_one (6734 : ZMod 15817)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15823 : Nat.Prime 15823 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15823 15822 1 3 [2, 3, 3, 3, 293]
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
    · apply IsUnit.of_mul_eq_one (7911 : ZMod 15823)
      decide
    · apply IsUnit.of_mul_eq_one (3035 : ZMod 15823)
      decide
    · apply IsUnit.of_mul_eq_one (12775 : ZMod 15823)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15859 : Nat.Prime 15859 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15859 15858 1 2 [2, 3, 3, 881]
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
    · apply IsUnit.of_mul_eq_one (7929 : ZMod 15859)
      decide
    · apply IsUnit.of_mul_eq_one (838 : ZMod 15859)
      decide
    · apply IsUnit.of_mul_eq_one (5185 : ZMod 15859)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15877 : Nat.Prime 15877 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15877 15876 1 5 [2, 2, 3, 3, 3, 3, 7, 7]
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
    · apply IsUnit.of_mul_eq_one (7938 : ZMod 15877)
      decide
    · apply IsUnit.of_mul_eq_one (2846 : ZMod 15877)
      decide
    · apply IsUnit.of_mul_eq_one (4620 : ZMod 15877)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15881 : Nat.Prime 15881 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15881 15880 1 3 [2, 2, 2, 5, 397]
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
    · apply IsUnit.of_mul_eq_one (7940 : ZMod 15881)
      decide
    · apply IsUnit.of_mul_eq_one (9416 : ZMod 15881)
      decide
    · apply IsUnit.of_mul_eq_one (3090 : ZMod 15881)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15887 : Nat.Prime 15887 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15887 15886 1 5 [2, 13, 13, 47]
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
    · apply IsUnit.of_mul_eq_one (7943 : ZMod 15887)
      decide
    · apply IsUnit.of_mul_eq_one (9880 : ZMod 15887)
      decide
    · apply IsUnit.of_mul_eq_one (11667 : ZMod 15887)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15889 : Nat.Prime 15889 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15889 15888 1 21 [2, 2, 2, 2, 3, 331]
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
    · apply IsUnit.of_mul_eq_one (7944 : ZMod 15889)
      decide
    · apply IsUnit.of_mul_eq_one (10481 : ZMod 15889)
      decide
    · apply IsUnit.of_mul_eq_one (2207 : ZMod 15889)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_15527_16318_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_16317 (p := 15803) (q := 15809) (by exact lowPrime_15809) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15809) (q := 15817) (by exact lowPrime_15817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15817) (q := 15823) (by exact lowPrime_15823) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15823) (q := 15859) (by exact lowPrime_15859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15859) (q := 15877) (by exact lowPrime_15877) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15877) (q := 15881) (by exact lowPrime_15881) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15881) (q := 15887) (by exact lowPrime_15887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_16317 (p := 15887) (q := 15889) (by exact lowPrime_15889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_15527_16318_part05_chain :
    DusartPrimeRowsChain 15803 15888 dusartPrimeRows_15527_16318_part05 := by
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
