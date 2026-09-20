import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! # Lower finite Dusart prefix chunk 236 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20147 : Nat.Prime 20147 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20147 20146 1 6 [2, 7, 1439]
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
    · apply IsUnit.of_mul_eq_one (10073 : ZMod 20147)
      decide
    · apply IsUnit.of_mul_eq_one (1299 : ZMod 20147)
      decide
    · apply IsUnit.of_mul_eq_one (12371 : ZMod 20147)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20149 : Nat.Prime 20149 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20149 20148 1 2 [2, 2, 3, 23, 73]
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
    · apply IsUnit.of_mul_eq_one (10074 : ZMod 20149)
      decide
    · apply IsUnit.of_mul_eq_one (4129 : ZMod 20149)
      decide
    · apply IsUnit.of_mul_eq_one (10732 : ZMod 20149)
      decide
    · apply IsUnit.of_mul_eq_one (4443 : ZMod 20149)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20161 : Nat.Prime 20161 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20161 20160 1 13 [2, 2, 2, 2, 2, 2, 3, 3, 5, 7]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · apply IsUnit.of_mul_eq_one (10080 : ZMod 20161)
      decide
    · apply IsUnit.of_mul_eq_one (8778 : ZMod 20161)
      decide
    · apply IsUnit.of_mul_eq_one (4369 : ZMod 20161)
      decide
    · apply IsUnit.of_mul_eq_one (7310 : ZMod 20161)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20173 : Nat.Prime 20173 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20173 20172 1 2 [2, 2, 3, 41, 41]
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
    · apply IsUnit.of_mul_eq_one (10086 : ZMod 20173)
      decide
    · apply IsUnit.of_mul_eq_one (10045 : ZMod 20173)
      decide
    · apply IsUnit.of_mul_eq_one (5767 : ZMod 20173)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20177 : Nat.Prime 20177 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20177 20176 1 3 [2, 2, 2, 2, 13, 97]
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
    · apply IsUnit.of_mul_eq_one (10088 : ZMod 20177)
      decide
    · apply IsUnit.of_mul_eq_one (6366 : ZMod 20177)
      decide
    · apply IsUnit.of_mul_eq_one (1102 : ZMod 20177)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20183 : Nat.Prime 20183 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20183 20182 1 5 [2, 10091]
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
    · apply IsUnit.of_mul_eq_one (10091 : ZMod 20183)
      decide
    · apply IsUnit.of_mul_eq_one (841 : ZMod 20183)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20201 : Nat.Prime 20201 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20201 20200 1 6 [2, 2, 2, 5, 5, 101]
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
    · apply IsUnit.of_mul_eq_one (10100 : ZMod 20201)
      decide
    · apply IsUnit.of_mul_eq_one (9752 : ZMod 20201)
      decide
    · apply IsUnit.of_mul_eq_one (4621 : ZMod 20201)
      decide
  · norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem lowPrime_20219 : Nat.Prime 20219 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20219 20218 1 2 [2, 11, 919]
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
    · apply IsUnit.of_mul_eq_one (10109 : ZMod 20219)
      decide
    · apply IsUnit.of_mul_eq_one (16500 : ZMod 20219)
      decide
    · apply IsUnit.of_mul_eq_one (14541 : ZMod 20219)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20143) (q := 20147) (by exact lowPrime_20147) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20147) (q := 20149) (by exact lowPrime_20149) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20149) (q := 20161) (by exact lowPrime_20161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20161) (q := 20173) (by exact lowPrime_20173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20173) (q := 20177) (by exact lowPrime_20177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20177) (q := 20183) (by exact lowPrime_20183) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20183) (q := 20201) (by exact lowPrime_20201) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20201) (q := 20219) (by exact lowPrime_20219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part04_chain :
    DusartPrimeRowsChain 20143 20218 dusartPrimeRows_19937_20958_part04 := by
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
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · apply DusartPrimeRowsChain.empty
                  norm_num [dusartPrimeRow_of_explicit_20952, dusartPrimeRow_of_explicit_right]
