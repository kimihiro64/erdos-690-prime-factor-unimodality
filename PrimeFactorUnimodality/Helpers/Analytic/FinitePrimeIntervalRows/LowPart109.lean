import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 109 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_10289 : Nat.Prime 10289 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10289 10288 1 3 [2, 2, 2, 2, 643]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 10289) ^ 5144 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5144 : ZMod 10289)
      decide
    · change IsUnit ((3 : ZMod 10289) ^ 5144 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5144 : ZMod 10289)
      decide
    · change IsUnit ((3 : ZMod 10289) ^ 5144 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5144 : ZMod 10289)
      decide
    · change IsUnit ((3 : ZMod 10289) ^ 5144 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5144 : ZMod 10289)
      decide
    · change IsUnit ((3 : ZMod 10289) ^ 16 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8718 : ZMod 10289)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10301 : Nat.Prime 10301 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10301 10300 1 2 [2, 2, 5, 5, 103]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 10301) ^ 5150 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5150 : ZMod 10301)
      decide
    · change IsUnit ((2 : ZMod 10301) ^ 5150 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5150 : ZMod 10301)
      decide
    · change IsUnit ((2 : ZMod 10301) ^ 2060 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9185 : ZMod 10301)
      decide
    · change IsUnit ((2 : ZMod 10301) ^ 2060 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9185 : ZMod 10301)
      decide
    · change IsUnit ((2 : ZMod 10301) ^ 100 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8186 : ZMod 10301)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10303 : Nat.Prime 10303 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10303 10302 1 3 [2, 3, 17, 101]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 10303) ^ 5151 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5151 : ZMod 10303)
      decide
    · change IsUnit ((3 : ZMod 10303) ^ 3434 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3400 : ZMod 10303)
      decide
    · change IsUnit ((3 : ZMod 10303) ^ 606 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1290 : ZMod 10303)
      decide
    · change IsUnit ((3 : ZMod 10303) ^ 102 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4197 : ZMod 10303)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10313 : Nat.Prime 10313 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10313 10312 1 3 [2, 2, 2, 1289]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 10313) ^ 5156 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5156 : ZMod 10313)
      decide
    · change IsUnit ((3 : ZMod 10313) ^ 5156 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5156 : ZMod 10313)
      decide
    · change IsUnit ((3 : ZMod 10313) ^ 5156 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5156 : ZMod 10313)
      decide
    · change IsUnit ((3 : ZMod 10313) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (665 : ZMod 10313)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10321 : Nat.Prime 10321 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10321 10320 1 7 [2, 2, 2, 2, 3, 5, 43]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((7 : ZMod 10321) ^ 5160 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5160 : ZMod 10321)
      decide
    · change IsUnit ((7 : ZMod 10321) ^ 5160 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5160 : ZMod 10321)
      decide
    · change IsUnit ((7 : ZMod 10321) ^ 5160 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5160 : ZMod 10321)
      decide
    · change IsUnit ((7 : ZMod 10321) ^ 5160 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5160 : ZMod 10321)
      decide
    · change IsUnit ((7 : ZMod 10321) ^ 3440 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7575 : ZMod 10321)
      decide
    · change IsUnit ((7 : ZMod 10321) ^ 2064 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2095 : ZMod 10321)
      decide
    · change IsUnit ((7 : ZMod 10321) ^ 240 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8568 : ZMod 10321)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10331 : Nat.Prime 10331 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10331 10330 1 2 [2, 5, 1033]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl
    · change IsUnit ((2 : ZMod 10331) ^ 5165 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5165 : ZMod 10331)
      decide
    · change IsUnit ((2 : ZMod 10331) ^ 2066 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10168 : ZMod 10331)
      decide
    · change IsUnit ((2 : ZMod 10331) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7160 : ZMod 10331)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10333 : Nat.Prime 10333 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10333 10332 1 5 [2, 2, 3, 3, 7, 41]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((5 : ZMod 10333) ^ 5166 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5166 : ZMod 10333)
      decide
    · change IsUnit ((5 : ZMod 10333) ^ 5166 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5166 : ZMod 10333)
      decide
    · change IsUnit ((5 : ZMod 10333) ^ 3444 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8077 : ZMod 10333)
      decide
    · change IsUnit ((5 : ZMod 10333) ^ 3444 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8077 : ZMod 10333)
      decide
    · change IsUnit ((5 : ZMod 10333) ^ 1476 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6570 : ZMod 10333)
      decide
    · change IsUnit ((5 : ZMod 10333) ^ 252 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6858 : ZMod 10333)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_10337 : Nat.Prime 10337 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 10337 10336 1 3 [2, 2, 2, 2, 2, 17, 19]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 10337) ^ 5168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5168 : ZMod 10337)
      decide
    · change IsUnit ((3 : ZMod 10337) ^ 5168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5168 : ZMod 10337)
      decide
    · change IsUnit ((3 : ZMod 10337) ^ 5168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5168 : ZMod 10337)
      decide
    · change IsUnit ((3 : ZMod 10337) ^ 5168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5168 : ZMod 10337)
      decide
    · change IsUnit ((3 : ZMod 10337) ^ 5168 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5168 : ZMod 10337)
      decide
    · change IsUnit ((3 : ZMod 10337) ^ 608 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4136 : ZMod 10337)
      decide
    · change IsUnit ((3 : ZMod 10337) ^ 544 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8238 : ZMod 10337)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9901_10426_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_10404 (p := 10273) (q := 10289) (by exact lowPrime_10289) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10289) (q := 10301) (by exact lowPrime_10301) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10301) (q := 10303) (by exact lowPrime_10303) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10303) (q := 10313) (by exact lowPrime_10313) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10313) (q := 10321) (by exact lowPrime_10321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10321) (q := 10331) (by exact lowPrime_10331) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10331) (q := 10333) (by exact lowPrime_10333) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_10404 (p := 10333) (q := 10337) (by exact lowPrime_10337) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9901_10426_part06_chain :
    DusartPrimeRowsChain 10273 10337 dusartPrimeRows_9901_10426_part06 := by
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
                  norm_num
