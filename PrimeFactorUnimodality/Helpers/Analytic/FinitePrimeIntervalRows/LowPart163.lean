import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 163 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_14249 : Nat.Prime 14249 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14249 14248 1 3 [2, 2, 2, 13, 137]
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
    · change IsUnit ((3 : ZMod 14249) ^ 7124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7124 : ZMod 14249)
      decide
    · change IsUnit ((3 : ZMod 14249) ^ 7124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7124 : ZMod 14249)
      decide
    · change IsUnit ((3 : ZMod 14249) ^ 7124 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7124 : ZMod 14249)
      decide
    · change IsUnit ((3 : ZMod 14249) ^ 1096 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11654 : ZMod 14249)
      decide
    · change IsUnit ((3 : ZMod 14249) ^ 104 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8319 : ZMod 14249)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14251 : Nat.Prime 14251 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14251 14250 1 3 [2, 3, 5, 5, 5, 19]
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
    · change IsUnit ((3 : ZMod 14251) ^ 7125 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7125 : ZMod 14251)
      decide
    · change IsUnit ((3 : ZMod 14251) ^ 4750 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2800 : ZMod 14251)
      decide
    · change IsUnit ((3 : ZMod 14251) ^ 2850 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8142 : ZMod 14251)
      decide
    · change IsUnit ((3 : ZMod 14251) ^ 2850 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8142 : ZMod 14251)
      decide
    · change IsUnit ((3 : ZMod 14251) ^ 2850 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8142 : ZMod 14251)
      decide
    · change IsUnit ((3 : ZMod 14251) ^ 750 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4205 : ZMod 14251)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14281 : Nat.Prime 14281 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14281 14280 1 19 [2, 2, 2, 3, 5, 7, 17]
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
    · change IsUnit ((19 : ZMod 14281) ^ 7140 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7140 : ZMod 14281)
      decide
    · change IsUnit ((19 : ZMod 14281) ^ 7140 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7140 : ZMod 14281)
      decide
    · change IsUnit ((19 : ZMod 14281) ^ 7140 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7140 : ZMod 14281)
      decide
    · change IsUnit ((19 : ZMod 14281) ^ 4760 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9560 : ZMod 14281)
      decide
    · change IsUnit ((19 : ZMod 14281) ^ 2856 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7194 : ZMod 14281)
      decide
    · change IsUnit ((19 : ZMod 14281) ^ 2040 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9439 : ZMod 14281)
      decide
    · change IsUnit ((19 : ZMod 14281) ^ 840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11150 : ZMod 14281)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14293 : Nat.Prime 14293 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14293 14292 1 6 [2, 2, 3, 3, 397]
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
    · change IsUnit ((6 : ZMod 14293) ^ 7146 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7146 : ZMod 14293)
      decide
    · change IsUnit ((6 : ZMod 14293) ^ 7146 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7146 : ZMod 14293)
      decide
    · change IsUnit ((6 : ZMod 14293) ^ 4764 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13679 : ZMod 14293)
      decide
    · change IsUnit ((6 : ZMod 14293) ^ 4764 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13679 : ZMod 14293)
      decide
    · change IsUnit ((6 : ZMod 14293) ^ 36 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1679 : ZMod 14293)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14303 : Nat.Prime 14303 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14303 14302 1 5 [2, 7151]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl
    · change IsUnit ((5 : ZMod 14303) ^ 7151 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7151 : ZMod 14303)
      decide
    · change IsUnit ((5 : ZMod 14303) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (596 : ZMod 14303)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14321 : Nat.Prime 14321 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14321 14320 1 3 [2, 2, 2, 2, 5, 179]
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
    · change IsUnit ((3 : ZMod 14321) ^ 7160 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7160 : ZMod 14321)
      decide
    · change IsUnit ((3 : ZMod 14321) ^ 7160 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7160 : ZMod 14321)
      decide
    · change IsUnit ((3 : ZMod 14321) ^ 7160 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7160 : ZMod 14321)
      decide
    · change IsUnit ((3 : ZMod 14321) ^ 7160 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7160 : ZMod 14321)
      decide
    · change IsUnit ((3 : ZMod 14321) ^ 2864 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13722 : ZMod 14321)
      decide
    · change IsUnit ((3 : ZMod 14321) ^ 80 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9776 : ZMod 14321)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14323 : Nat.Prime 14323 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14323 14322 1 5 [2, 3, 7, 11, 31]
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
    · change IsUnit ((5 : ZMod 14323) ^ 7161 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7161 : ZMod 14323)
      decide
    · change IsUnit ((5 : ZMod 14323) ^ 4774 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12779 : ZMod 14323)
      decide
    · change IsUnit ((5 : ZMod 14323) ^ 2046 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10494 : ZMod 14323)
      decide
    · change IsUnit ((5 : ZMod 14323) ^ 1302 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2467 : ZMod 14323)
      decide
    · change IsUnit ((5 : ZMod 14323) ^ 462 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2051 : ZMod 14323)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_14327 : Nat.Prime 14327 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 14327 14326 1 5 [2, 13, 19, 29]
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
    · change IsUnit ((5 : ZMod 14327) ^ 7163 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7163 : ZMod 14327)
      decide
    · change IsUnit ((5 : ZMod 14327) ^ 1102 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11573 : ZMod 14327)
      decide
    · change IsUnit ((5 : ZMod 14327) ^ 754 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7610 : ZMod 14327)
      decide
    · change IsUnit ((5 : ZMod 14327) ^ 494 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6669 : ZMod 14327)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14051_14766_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14764 (p := 14243) (q := 14249) (by exact lowPrime_14249) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14249) (q := 14251) (by exact lowPrime_14251) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14251) (q := 14281) (by exact lowPrime_14281) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14281) (q := 14293) (by exact lowPrime_14293) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14293) (q := 14303) (by exact lowPrime_14303) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14303) (q := 14321) (by exact lowPrime_14321) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14321) (q := 14323) (by exact lowPrime_14323) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14764 (p := 14323) (q := 14327) (by exact lowPrime_14327) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14051_14766_part03_chain :
    DusartPrimeRowsChain 14243 14327 dusartPrimeRows_14051_14766_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · norm_num [dusartPrimeRow_of_explicit_14764]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · norm_num [dusartPrimeRow_of_explicit_14764]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · norm_num [dusartPrimeRow_of_explicit_14764]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · norm_num [dusartPrimeRow_of_explicit_14764]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · norm_num [dusartPrimeRow_of_explicit_14764]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · norm_num [dusartPrimeRow_of_explicit_14764]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · norm_num [dusartPrimeRow_of_explicit_14764]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · norm_num [dusartPrimeRow_of_explicit_14764]
                · apply DusartPrimeRowsChain.empty
                  norm_num
