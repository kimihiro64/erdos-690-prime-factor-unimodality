import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 176 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_15161 : Nat.Prime 15161 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15161 15160 1 3 [2, 2, 2, 5, 379]
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
    · change IsUnit ((3 : ZMod 15161) ^ 7580 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7580 : ZMod 15161)
      decide
    · change IsUnit ((3 : ZMod 15161) ^ 7580 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7580 : ZMod 15161)
      decide
    · change IsUnit ((3 : ZMod 15161) ^ 7580 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7580 : ZMod 15161)
      decide
    · change IsUnit ((3 : ZMod 15161) ^ 3032 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13883 : ZMod 15161)
      decide
    · change IsUnit ((3 : ZMod 15161) ^ 40 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15016 : ZMod 15161)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15173 : Nat.Prime 15173 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15173 15172 1 2 [2, 2, 3793]
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
    · change IsUnit ((2 : ZMod 15173) ^ 7586 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7586 : ZMod 15173)
      decide
    · change IsUnit ((2 : ZMod 15173) ^ 7586 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7586 : ZMod 15173)
      decide
    · change IsUnit ((2 : ZMod 15173) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13150 : ZMod 15173)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15187 : Nat.Prime 15187 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15187 15186 1 2 [2, 3, 2531]
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
    · change IsUnit ((2 : ZMod 15187) ^ 7593 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7593 : ZMod 15187)
      decide
    · change IsUnit ((2 : ZMod 15187) ^ 5062 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4741 : ZMod 15187)
      decide
    · change IsUnit ((2 : ZMod 15187) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11330 : ZMod 15187)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15193 : Nat.Prime 15193 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15193 15192 1 5 [2, 2, 2, 3, 3, 211]
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
    · change IsUnit ((5 : ZMod 15193) ^ 7596 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7596 : ZMod 15193)
      decide
    · change IsUnit ((5 : ZMod 15193) ^ 7596 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7596 : ZMod 15193)
      decide
    · change IsUnit ((5 : ZMod 15193) ^ 7596 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7596 : ZMod 15193)
      decide
    · change IsUnit ((5 : ZMod 15193) ^ 5064 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6594 : ZMod 15193)
      decide
    · change IsUnit ((5 : ZMod 15193) ^ 5064 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6594 : ZMod 15193)
      decide
    · change IsUnit ((5 : ZMod 15193) ^ 72 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (644 : ZMod 15193)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15199 : Nat.Prime 15199 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15199 15198 1 6 [2, 3, 17, 149]
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
    · change IsUnit ((6 : ZMod 15199) ^ 7599 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7599 : ZMod 15199)
      decide
    · change IsUnit ((6 : ZMod 15199) ^ 5066 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6804 : ZMod 15199)
      decide
    · change IsUnit ((6 : ZMod 15199) ^ 894 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14255 : ZMod 15199)
      decide
    · change IsUnit ((6 : ZMod 15199) ^ 102 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13016 : ZMod 15199)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15217 : Nat.Prime 15217 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15217 15216 1 10 [2, 2, 2, 2, 3, 317]
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
    · change IsUnit ((10 : ZMod 15217) ^ 7608 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7608 : ZMod 15217)
      decide
    · change IsUnit ((10 : ZMod 15217) ^ 7608 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7608 : ZMod 15217)
      decide
    · change IsUnit ((10 : ZMod 15217) ^ 7608 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7608 : ZMod 15217)
      decide
    · change IsUnit ((10 : ZMod 15217) ^ 7608 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7608 : ZMod 15217)
      decide
    · change IsUnit ((10 : ZMod 15217) ^ 5072 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10432 : ZMod 15217)
      decide
    · change IsUnit ((10 : ZMod 15217) ^ 48 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1785 : ZMod 15217)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15227 : Nat.Prime 15227 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15227 15226 1 2 [2, 23, 331]
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
    · change IsUnit ((2 : ZMod 15227) ^ 7613 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7613 : ZMod 15227)
      decide
    · change IsUnit ((2 : ZMod 15227) ^ 662 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8670 : ZMod 15227)
      decide
    · change IsUnit ((2 : ZMod 15227) ^ 46 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3267 : ZMod 15227)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_15233 : Nat.Prime 15233 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 15233 15232 1 3 [2, 2, 2, 2, 2, 2, 2, 7, 17]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((3 : ZMod 15233) ^ 7616 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7616 : ZMod 15233)
      decide
    · change IsUnit ((3 : ZMod 15233) ^ 7616 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7616 : ZMod 15233)
      decide
    · change IsUnit ((3 : ZMod 15233) ^ 7616 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7616 : ZMod 15233)
      decide
    · change IsUnit ((3 : ZMod 15233) ^ 7616 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7616 : ZMod 15233)
      decide
    · change IsUnit ((3 : ZMod 15233) ^ 7616 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7616 : ZMod 15233)
      decide
    · change IsUnit ((3 : ZMod 15233) ^ 7616 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7616 : ZMod 15233)
      decide
    · change IsUnit ((3 : ZMod 15233) ^ 7616 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7616 : ZMod 15233)
      decide
    · change IsUnit ((3 : ZMod 15233) ^ 2176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7806 : ZMod 15233)
      decide
    · change IsUnit ((3 : ZMod 15233) ^ 896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3855 : ZMod 15233)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_14767_15526_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_15521 (p := 15149) (q := 15161) (by exact lowPrime_15161) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15161) (q := 15173) (by exact lowPrime_15173) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15173) (q := 15187) (by exact lowPrime_15187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15187) (q := 15193) (by exact lowPrime_15193) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15193) (q := 15199) (by exact lowPrime_15199) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15199) (q := 15217) (by exact lowPrime_15217) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15217) (q := 15227) (by exact lowPrime_15227) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_15521 (p := 15227) (q := 15233) (by exact lowPrime_15233) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_14767_15526_part06_chain :
    DusartPrimeRowsChain 15149 15233 dusartPrimeRows_14767_15526_part06 := by
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
                  norm_num
