import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 271 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_17167 : Nat.Prime 17167 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17167 17166 1 3 [2, 3, 2861]
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
    · change IsUnit ((3 : ZMod 17167) ^ 8583 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8583 : ZMod 17167)
      decide
    · change IsUnit ((3 : ZMod 17167) ^ 5722 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1988 : ZMod 17167)
      decide
    · change IsUnit ((3 : ZMod 17167) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9456 : ZMod 17167)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17183 : Nat.Prime 17183 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17183 17182 1 5 [2, 11, 11, 71]
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
    · change IsUnit ((5 : ZMod 17183) ^ 8591 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8591 : ZMod 17183)
      decide
    · change IsUnit ((5 : ZMod 17183) ^ 1562 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8757 : ZMod 17183)
      decide
    · change IsUnit ((5 : ZMod 17183) ^ 1562 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8757 : ZMod 17183)
      decide
    · change IsUnit ((5 : ZMod 17183) ^ 242 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6133 : ZMod 17183)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17189 : Nat.Prime 17189 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17189 17188 1 2 [2, 2, 4297]
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
    · change IsUnit ((2 : ZMod 17189) ^ 8594 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8594 : ZMod 17189)
      decide
    · change IsUnit ((2 : ZMod 17189) ^ 8594 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8594 : ZMod 17189)
      decide
    · change IsUnit ((2 : ZMod 17189) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1146 : ZMod 17189)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17191 : Nat.Prime 17191 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17191 17190 1 3 [2, 3, 3, 5, 191]
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
    · change IsUnit ((3 : ZMod 17191) ^ 8595 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8595 : ZMod 17191)
      decide
    · change IsUnit ((3 : ZMod 17191) ^ 5730 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10853 : ZMod 17191)
      decide
    · change IsUnit ((3 : ZMod 17191) ^ 5730 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10853 : ZMod 17191)
      decide
    · change IsUnit ((3 : ZMod 17191) ^ 3438 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14803 : ZMod 17191)
      decide
    · change IsUnit ((3 : ZMod 17191) ^ 90 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10121 : ZMod 17191)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17203 : Nat.Prime 17203 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17203 17202 1 2 [2, 3, 47, 61]
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
    · change IsUnit ((2 : ZMod 17203) ^ 8601 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8601 : ZMod 17203)
      decide
    · change IsUnit ((2 : ZMod 17203) ^ 5734 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15740 : ZMod 17203)
      decide
    · change IsUnit ((2 : ZMod 17203) ^ 366 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (191 : ZMod 17203)
      decide
    · change IsUnit ((2 : ZMod 17203) ^ 282 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6272 : ZMod 17203)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17207 : Nat.Prime 17207 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17207 17206 1 5 [2, 7, 1229]
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
    · change IsUnit ((5 : ZMod 17207) ^ 8603 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8603 : ZMod 17207)
      decide
    · change IsUnit ((5 : ZMod 17207) ^ 2458 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4719 : ZMod 17207)
      decide
    · change IsUnit ((5 : ZMod 17207) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5531 : ZMod 17207)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17209 : Nat.Prime 17209 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17209 17208 1 14 [2, 2, 2, 3, 3, 239]
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
    · change IsUnit ((14 : ZMod 17209) ^ 8604 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8604 : ZMod 17209)
      decide
    · change IsUnit ((14 : ZMod 17209) ^ 8604 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8604 : ZMod 17209)
      decide
    · change IsUnit ((14 : ZMod 17209) ^ 8604 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8604 : ZMod 17209)
      decide
    · change IsUnit ((14 : ZMod 17209) ^ 5736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16486 : ZMod 17209)
      decide
    · change IsUnit ((14 : ZMod 17209) ^ 5736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16486 : ZMod 17209)
      decide
    · change IsUnit ((14 : ZMod 17209) ^ 72 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6719 : ZMod 17209)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_17231 : Nat.Prime 17231 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 17231 17230 1 13 [2, 5, 1723]
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
    · change IsUnit ((13 : ZMod 17231) ^ 8615 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8615 : ZMod 17231)
      decide
    · change IsUnit ((13 : ZMod 17231) ^ 3446 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4035 : ZMod 17231)
      decide
    · change IsUnit ((13 : ZMod 17231) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16704 : ZMod 17231)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_17159_18040_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18033 (p := 17159) (q := 17167) (by exact lowPrime_17167) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17167) (q := 17183) (by exact lowPrime_17183) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17183) (q := 17189) (by exact lowPrime_17189) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17189) (q := 17191) (by exact lowPrime_17191) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17191) (q := 17203) (by exact lowPrime_17203) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17203) (q := 17207) (by exact lowPrime_17207) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17207) (q := 17209) (by exact lowPrime_17209) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18033 (p := 17209) (q := 17231) (by exact lowPrime_17231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_17159_18040_part01_chain :
    DusartPrimeRowsChain 17159 17231 dusartPrimeRows_17159_18040_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · norm_num [dusartPrimeRow_of_explicit_18033]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · norm_num [dusartPrimeRow_of_explicit_18033]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · norm_num [dusartPrimeRow_of_explicit_18033]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · norm_num [dusartPrimeRow_of_explicit_18033]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · norm_num [dusartPrimeRow_of_explicit_18033]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · norm_num [dusartPrimeRow_of_explicit_18033]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · norm_num [dusartPrimeRow_of_explicit_18033]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · norm_num [dusartPrimeRow_of_explicit_18033]
                · apply DusartPrimeRowsChain.empty
                  norm_num
