import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 92 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9127 : Nat.Prime 9127 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9127 9126 1 3 [2, 3, 3, 3, 13, 13]
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
    · apply IsUnit.of_mul_eq_one (4563 : ZMod 9127)
      decide
    · apply IsUnit.of_mul_eq_one (8123 : ZMod 9127)
      decide
    · apply IsUnit.of_mul_eq_one (153 : ZMod 9127)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9133 : Nat.Prime 9133 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9133 9132 1 6 [2, 2, 3, 761]
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
    · apply IsUnit.of_mul_eq_one (4566 : ZMod 9133)
      decide
    · apply IsUnit.of_mul_eq_one (7354 : ZMod 9133)
      decide
    · apply IsUnit.of_mul_eq_one (7856 : ZMod 9133)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9137 : Nat.Prime 9137 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9137 9136 1 3 [2, 2, 2, 2, 571]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (4568 : ZMod 9137)
      decide
    · apply IsUnit.of_mul_eq_one (4211 : ZMod 9137)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9151 : Nat.Prime 9151 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9151 9150 1 3 [2, 3, 5, 5, 61]
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
    · apply IsUnit.of_mul_eq_one (4575 : ZMod 9151)
      decide
    · apply IsUnit.of_mul_eq_one (6492 : ZMod 9151)
      decide
    · apply IsUnit.of_mul_eq_one (8634 : ZMod 9151)
      decide
    · apply IsUnit.of_mul_eq_one (6104 : ZMod 9151)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9157 : Nat.Prime 9157 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9157 9156 1 6 [2, 2, 3, 7, 109]
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
    · apply IsUnit.of_mul_eq_one (4578 : ZMod 9157)
      decide
    · apply IsUnit.of_mul_eq_one (8725 : ZMod 9157)
      decide
    · apply IsUnit.of_mul_eq_one (6761 : ZMod 9157)
      decide
    · apply IsUnit.of_mul_eq_one (7139 : ZMod 9157)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9161 : Nat.Prime 9161 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9161 9160 1 3 [2, 2, 2, 5, 229]
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
    · apply IsUnit.of_mul_eq_one (4580 : ZMod 9161)
      decide
    · apply IsUnit.of_mul_eq_one (6445 : ZMod 9161)
      decide
    · apply IsUnit.of_mul_eq_one (6446 : ZMod 9161)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9173 : Nat.Prime 9173 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9173 9172 1 2 [2, 2, 2293]
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
    rcases hq with rfl | rfl
    · apply IsUnit.of_mul_eq_one (4586 : ZMod 9173)
      decide
    · apply IsUnit.of_mul_eq_one (7950 : ZMod 9173)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_9181 : Nat.Prime 9181 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9181 9180 1 2 [2, 2, 3, 3, 3, 5, 17]
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
    · apply IsUnit.of_mul_eq_one (4590 : ZMod 9181)
      decide
    · apply IsUnit.of_mul_eq_one (8844 : ZMod 9181)
      decide
    · apply IsUnit.of_mul_eq_one (2450 : ZMod 9181)
      decide
    · apply IsUnit.of_mul_eq_one (4952 : ZMod 9181)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8963_9418_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9414 (p := 9109) (q := 9127) (by exact lowPrime_9127) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9127) (q := 9133) (by exact lowPrime_9133) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9133) (q := 9137) (by exact lowPrime_9137) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9137) (q := 9151) (by exact lowPrime_9151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9151) (q := 9157) (by exact lowPrime_9157) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9157) (q := 9161) (by exact lowPrime_9161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9161) (q := 9173) (by exact lowPrime_9173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9414 (p := 9173) (q := 9181) (by exact lowPrime_9181) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8963_9418_part03_chain :
    DusartPrimeRowsChain 9109 9180 dusartPrimeRows_8963_9418_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · norm_num [dusartPrimeRow_of_explicit_9414]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · norm_num [dusartPrimeRow_of_explicit_9414]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · norm_num [dusartPrimeRow_of_explicit_9414]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · norm_num [dusartPrimeRow_of_explicit_9414]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · norm_num [dusartPrimeRow_of_explicit_9414]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · norm_num [dusartPrimeRow_of_explicit_9414]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · norm_num [dusartPrimeRow_of_explicit_9414]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · norm_num [dusartPrimeRow_of_explicit_9414]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_9414, dusartPrimeRow_of_explicit_right]
