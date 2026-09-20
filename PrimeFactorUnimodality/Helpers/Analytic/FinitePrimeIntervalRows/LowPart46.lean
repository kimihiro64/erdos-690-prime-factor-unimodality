import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 46 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6143 : Nat.Prime 6143 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6143 6142 1 5 [2, 37, 83]
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
    · apply IsUnit.of_mul_eq_one (3071 : ZMod 6143)
      decide
    · apply IsUnit.of_mul_eq_one (1546 : ZMod 6143)
      decide
    · apply IsUnit.of_mul_eq_one (2460 : ZMod 6143)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6151 : Nat.Prime 6151 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6151 6150 1 3 [2, 3, 5, 5, 41]
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
    · apply IsUnit.of_mul_eq_one (3075 : ZMod 6151)
      decide
    · apply IsUnit.of_mul_eq_one (4031 : ZMod 6151)
      decide
    · apply IsUnit.of_mul_eq_one (5565 : ZMod 6151)
      decide
    · apply IsUnit.of_mul_eq_one (4265 : ZMod 6151)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6163 : Nat.Prime 6163 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6163 6162 1 3 [2, 3, 13, 79]
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
    · apply IsUnit.of_mul_eq_one (3081 : ZMod 6163)
      decide
    · apply IsUnit.of_mul_eq_one (2080 : ZMod 6163)
      decide
    · apply IsUnit.of_mul_eq_one (2165 : ZMod 6163)
      decide
    · apply IsUnit.of_mul_eq_one (2693 : ZMod 6163)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6173 : Nat.Prime 6173 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6173 6172 1 2 [2, 2, 1543]
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
    · apply IsUnit.of_mul_eq_one (3086 : ZMod 6173)
      decide
    · apply IsUnit.of_mul_eq_one (5350 : ZMod 6173)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6197 : Nat.Prime 6197 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6197 6196 1 2 [2, 2, 1549]
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
    · apply IsUnit.of_mul_eq_one (3098 : ZMod 6197)
      decide
    · apply IsUnit.of_mul_eq_one (2892 : ZMod 6197)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6199 : Nat.Prime 6199 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6199 6198 1 3 [2, 3, 1033]
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
    · apply IsUnit.of_mul_eq_one (3099 : ZMod 6199)
      decide
    · apply IsUnit.of_mul_eq_one (5014 : ZMod 6199)
      decide
    · apply IsUnit.of_mul_eq_one (281 : ZMod 6199)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6203 : Nat.Prime 6203 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6203 6202 1 2 [2, 7, 443]
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
    · apply IsUnit.of_mul_eq_one (3101 : ZMod 6203)
      decide
    · apply IsUnit.of_mul_eq_one (5943 : ZMod 6203)
      decide
    · apply IsUnit.of_mul_eq_one (666 : ZMod 6203)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_6211 : Nat.Prime 6211 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6211 6210 1 2 [2, 3, 3, 3, 5, 23]
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
    · apply IsUnit.of_mul_eq_one (3105 : ZMod 6211)
      decide
    · apply IsUnit.of_mul_eq_one (45 : ZMod 6211)
      decide
    · apply IsUnit.of_mul_eq_one (4797 : ZMod 6211)
      decide
    · apply IsUnit.of_mul_eq_one (1180 : ZMod 6211)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6007_6310_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_6310 (p := 6133) (q := 6143) (by exact lowPrime_6143) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6143) (q := 6151) (by exact lowPrime_6151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6151) (q := 6163) (by exact lowPrime_6163) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6163) (q := 6173) (by exact lowPrime_6173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6173) (q := 6197) (by exact lowPrime_6197) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6197) (q := 6199) (by exact lowPrime_6199) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6199) (q := 6203) (by exact lowPrime_6203) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_6310 (p := 6203) (q := 6211) (by exact lowPrime_6211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6007_6310_part03_chain :
    DusartPrimeRowsChain 6133 6210 dusartPrimeRows_6007_6310_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · norm_num [dusartPrimeRow_of_explicit_6310]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · norm_num [dusartPrimeRow_of_explicit_6310]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · norm_num [dusartPrimeRow_of_explicit_6310]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · norm_num [dusartPrimeRow_of_explicit_6310]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · norm_num [dusartPrimeRow_of_explicit_6310]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · norm_num [dusartPrimeRow_of_explicit_6310]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · norm_num [dusartPrimeRow_of_explicit_6310]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · norm_num [dusartPrimeRow_of_explicit_6310]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_6310, dusartPrimeRow_of_explicit_right]
