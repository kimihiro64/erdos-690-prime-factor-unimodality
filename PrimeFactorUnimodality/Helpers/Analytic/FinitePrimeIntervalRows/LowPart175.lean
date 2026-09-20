import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 175 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15091 : Nat.Prime 15091 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15091 15090 1 2 [2, 3, 5, 503]
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
    · apply IsUnit.of_mul_eq_one (7545 : ZMod 15091)
      decide
    · apply IsUnit.of_mul_eq_one (13860 : ZMod 15091)
      decide
    · apply IsUnit.of_mul_eq_one (3229 : ZMod 15091)
      decide
    · apply IsUnit.of_mul_eq_one (1080 : ZMod 15091)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15101 : Nat.Prime 15101 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15101 15100 1 2 [2, 2, 5, 5, 151]
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
    · apply IsUnit.of_mul_eq_one (7550 : ZMod 15101)
      decide
    · apply IsUnit.of_mul_eq_one (4599 : ZMod 15101)
      decide
    · apply IsUnit.of_mul_eq_one (7219 : ZMod 15101)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15107 : Nat.Prime 15107 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15107 15106 1 2 [2, 7, 13, 83]
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
    · apply IsUnit.of_mul_eq_one (7553 : ZMod 15107)
      decide
    · apply IsUnit.of_mul_eq_one (6935 : ZMod 15107)
      decide
    · apply IsUnit.of_mul_eq_one (6728 : ZMod 15107)
      decide
    · apply IsUnit.of_mul_eq_one (13015 : ZMod 15107)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15121 : Nat.Prime 15121 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15121 15120 1 11 [2, 2, 2, 2, 3, 3, 3, 5, 7]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (7560 : ZMod 15121)
      decide
    · apply IsUnit.of_mul_eq_one (2609 : ZMod 15121)
      decide
    · apply IsUnit.of_mul_eq_one (14801 : ZMod 15121)
      decide
    · apply IsUnit.of_mul_eq_one (12872 : ZMod 15121)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15131 : Nat.Prime 15131 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15131 15130 1 2 [2, 5, 17, 89]
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
    · apply IsUnit.of_mul_eq_one (7565 : ZMod 15131)
      decide
    · apply IsUnit.of_mul_eq_one (12344 : ZMod 15131)
      decide
    · apply IsUnit.of_mul_eq_one (7324 : ZMod 15131)
      decide
    · apply IsUnit.of_mul_eq_one (9054 : ZMod 15131)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15137 : Nat.Prime 15137 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15137 15136 1 3 [2, 2, 2, 2, 2, 11, 43]
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
    · apply IsUnit.of_mul_eq_one (7568 : ZMod 15137)
      decide
    · apply IsUnit.of_mul_eq_one (4734 : ZMod 15137)
      decide
    · apply IsUnit.of_mul_eq_one (2214 : ZMod 15137)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15139 : Nat.Prime 15139 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15139 15138 1 2 [2, 3, 3, 29, 29]
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
    · apply IsUnit.of_mul_eq_one (7569 : ZMod 15139)
      decide
    · apply IsUnit.of_mul_eq_one (13255 : ZMod 15139)
      decide
    · apply IsUnit.of_mul_eq_one (7360 : ZMod 15139)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_15149 : Nat.Prime 15149 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15149 15148 1 2 [2, 2, 7, 541]
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
    · apply IsUnit.of_mul_eq_one (7574 : ZMod 15149)
      decide
    · apply IsUnit.of_mul_eq_one (7916 : ZMod 15149)
      decide
    · apply IsUnit.of_mul_eq_one (13733 : ZMod 15149)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15083) (q := 15091) (by exact lowPrime_15091) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15091) (q := 15101) (by exact lowPrime_15101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15101) (q := 15107) (by exact lowPrime_15107) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15107) (q := 15121) (by exact lowPrime_15121) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15121) (q := 15131) (by exact lowPrime_15131) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15131) (q := 15137) (by exact lowPrime_15137) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15137) (q := 15139) (by exact lowPrime_15139) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15139) (q := 15149) (by exact lowPrime_15149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part05_chain :
    DusartPrimeRowsChain 15083 15148 dusartPrimeRows_14767_15526_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · norm_num [dusartPrimeRow_of_explicit_15521]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · norm_num [dusartPrimeRow_of_explicit_15521]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · norm_num [dusartPrimeRow_of_explicit_15521]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · norm_num [dusartPrimeRow_of_explicit_15521]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · norm_num [dusartPrimeRow_of_explicit_15521]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · norm_num [dusartPrimeRow_of_explicit_15521]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · norm_num [dusartPrimeRow_of_explicit_15521]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · norm_num [dusartPrimeRow_of_explicit_15521]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_15521, dusartPrimeRow_of_explicit_right]
