import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 107 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10151 : Nat.Prime 10151 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10151 10150 1 7 [2, 5, 5, 7, 29]
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
    · apply IsUnit.of_mul_eq_one (5075 : ZMod 10151)
      decide
    · apply IsUnit.of_mul_eq_one (757 : ZMod 10151)
      decide
    · apply IsUnit.of_mul_eq_one (3042 : ZMod 10151)
      decide
    · apply IsUnit.of_mul_eq_one (120 : ZMod 10151)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10159 : Nat.Prime 10159 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10159 10158 1 3 [2, 3, 1693]
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
    · apply IsUnit.of_mul_eq_one (5079 : ZMod 10159)
      decide
    · apply IsUnit.of_mul_eq_one (4917 : ZMod 10159)
      decide
    · apply IsUnit.of_mul_eq_one (4926 : ZMod 10159)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10163 : Nat.Prime 10163 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10163 10162 1 2 [2, 5081]
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
    · apply IsUnit.of_mul_eq_one (5081 : ZMod 10163)
      decide
    · apply IsUnit.of_mul_eq_one (3388 : ZMod 10163)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10169 : Nat.Prime 10169 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10169 10168 1 3 [2, 2, 2, 31, 41]
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
    · apply IsUnit.of_mul_eq_one (5084 : ZMod 10169)
      decide
    · apply IsUnit.of_mul_eq_one (10036 : ZMod 10169)
      decide
    · apply IsUnit.of_mul_eq_one (8135 : ZMod 10169)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10177 : Nat.Prime 10177 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10177 10176 1 7 [2, 2, 2, 2, 2, 2, 3, 53]
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
    · apply IsUnit.of_mul_eq_one (5088 : ZMod 10177)
      decide
    · apply IsUnit.of_mul_eq_one (5193 : ZMod 10177)
      decide
    · apply IsUnit.of_mul_eq_one (259 : ZMod 10177)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10181 : Nat.Prime 10181 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10181 10180 1 2 [2, 2, 5, 509]
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
    · apply IsUnit.of_mul_eq_one (5090 : ZMod 10181)
      decide
    · apply IsUnit.of_mul_eq_one (7224 : ZMod 10181)
      decide
    · apply IsUnit.of_mul_eq_one (3743 : ZMod 10181)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10193 : Nat.Prime 10193 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10193 10192 1 3 [2, 2, 2, 2, 7, 7, 13]
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
    · apply IsUnit.of_mul_eq_one (5096 : ZMod 10193)
      decide
    · apply IsUnit.of_mul_eq_one (2241 : ZMod 10193)
      decide
    · apply IsUnit.of_mul_eq_one (7140 : ZMod 10193)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_10211 : Nat.Prime 10211 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10211 10210 1 6 [2, 5, 1021]
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
    · apply IsUnit.of_mul_eq_one (5105 : ZMod 10211)
      decide
    · apply IsUnit.of_mul_eq_one (3206 : ZMod 10211)
      decide
    · apply IsUnit.of_mul_eq_one (8076 : ZMod 10211)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10141) (q := 10151) (by exact lowPrime_10151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10151) (q := 10159) (by exact lowPrime_10159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10159) (q := 10163) (by exact lowPrime_10163) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10163) (q := 10169) (by exact lowPrime_10169) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10169) (q := 10177) (by exact lowPrime_10177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10177) (q := 10181) (by exact lowPrime_10181) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10181) (q := 10193) (by exact lowPrime_10193) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10193) (q := 10211) (by exact lowPrime_10211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part04_chain :
    DusartPrimeRowsChain 10141 10210 dusartPrimeRows_9901_10426_part04 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · norm_num [dusartPrimeRow_of_explicit_10404]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · norm_num [dusartPrimeRow_of_explicit_10404]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · norm_num [dusartPrimeRow_of_explicit_10404]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · norm_num [dusartPrimeRow_of_explicit_10404]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · norm_num [dusartPrimeRow_of_explicit_10404]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · norm_num [dusartPrimeRow_of_explicit_10404]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · norm_num [dusartPrimeRow_of_explicit_10404]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · norm_num [dusartPrimeRow_of_explicit_10404]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_10404, dusartPrimeRow_of_explicit_right]
