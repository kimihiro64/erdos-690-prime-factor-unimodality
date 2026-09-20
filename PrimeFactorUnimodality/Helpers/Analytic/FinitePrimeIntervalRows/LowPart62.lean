import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 62 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_7129 : Nat.Prime 7129 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7129 7128 1 7 [2, 2, 2, 3, 3, 3, 3, 11]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((7 : ZMod 7129) ^ 3564 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3564 : ZMod 7129)
      decide
    · change IsUnit ((7 : ZMod 7129) ^ 3564 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3564 : ZMod 7129)
      decide
    · change IsUnit ((7 : ZMod 7129) ^ 3564 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3564 : ZMod 7129)
      decide
    · change IsUnit ((7 : ZMod 7129) ^ 2376 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (416 : ZMod 7129)
      decide
    · change IsUnit ((7 : ZMod 7129) ^ 2376 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (416 : ZMod 7129)
      decide
    · change IsUnit ((7 : ZMod 7129) ^ 2376 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (416 : ZMod 7129)
      decide
    · change IsUnit ((7 : ZMod 7129) ^ 2376 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (416 : ZMod 7129)
      decide
    · change IsUnit ((7 : ZMod 7129) ^ 648 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3828 : ZMod 7129)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7151 : Nat.Prime 7151 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7151 7150 1 7 [2, 5, 5, 11, 13]
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
    · change IsUnit ((7 : ZMod 7151) ^ 3575 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3575 : ZMod 7151)
      decide
    · change IsUnit ((7 : ZMod 7151) ^ 1430 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7117 : ZMod 7151)
      decide
    · change IsUnit ((7 : ZMod 7151) ^ 1430 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7117 : ZMod 7151)
      decide
    · change IsUnit ((7 : ZMod 7151) ^ 650 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7054 : ZMod 7151)
      decide
    · change IsUnit ((7 : ZMod 7151) ^ 550 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (546 : ZMod 7151)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7159 : Nat.Prime 7159 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7159 7158 1 3 [2, 3, 1193]
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
    · change IsUnit ((3 : ZMod 7159) ^ 3579 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3579 : ZMod 7159)
      decide
    · change IsUnit ((3 : ZMod 7159) ^ 2386 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3812 : ZMod 7159)
      decide
    · change IsUnit ((3 : ZMod 7159) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3550 : ZMod 7159)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7177 : Nat.Prime 7177 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7177 7176 1 10 [2, 2, 2, 3, 13, 23]
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
    · change IsUnit ((10 : ZMod 7177) ^ 3588 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3588 : ZMod 7177)
      decide
    · change IsUnit ((10 : ZMod 7177) ^ 3588 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3588 : ZMod 7177)
      decide
    · change IsUnit ((10 : ZMod 7177) ^ 3588 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3588 : ZMod 7177)
      decide
    · change IsUnit ((10 : ZMod 7177) ^ 2392 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (679 : ZMod 7177)
      decide
    · change IsUnit ((10 : ZMod 7177) ^ 552 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (175 : ZMod 7177)
      decide
    · change IsUnit ((10 : ZMod 7177) ^ 312 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3766 : ZMod 7177)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7187 : Nat.Prime 7187 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7187 7186 1 2 [2, 3593]
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
    · change IsUnit ((2 : ZMod 7187) ^ 3593 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3593 : ZMod 7187)
      decide
    · change IsUnit ((2 : ZMod 7187) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2396 : ZMod 7187)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7193 : Nat.Prime 7193 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7193 7192 1 3 [2, 2, 2, 29, 31]
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
    · change IsUnit ((3 : ZMod 7193) ^ 3596 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3596 : ZMod 7193)
      decide
    · change IsUnit ((3 : ZMod 7193) ^ 3596 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3596 : ZMod 7193)
      decide
    · change IsUnit ((3 : ZMod 7193) ^ 3596 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3596 : ZMod 7193)
      decide
    · change IsUnit ((3 : ZMod 7193) ^ 248 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2978 : ZMod 7193)
      decide
    · change IsUnit ((3 : ZMod 7193) ^ 232 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (722 : ZMod 7193)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7207 : Nat.Prime 7207 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7207 7206 1 3 [2, 3, 1201]
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
    · change IsUnit ((3 : ZMod 7207) ^ 3603 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3603 : ZMod 7207)
      decide
    · change IsUnit ((3 : ZMod 7207) ^ 2402 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5417 : ZMod 7207)
      decide
    · change IsUnit ((3 : ZMod 7207) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3653 : ZMod 7207)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7211 : Nat.Prime 7211 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7211 7210 1 2 [2, 5, 7, 103]
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
    · change IsUnit ((2 : ZMod 7211) ^ 3605 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3605 : ZMod 7211)
      decide
    · change IsUnit ((2 : ZMod 7211) ^ 1442 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2383 : ZMod 7211)
      decide
    · change IsUnit ((2 : ZMod 7211) ^ 1030 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1978 : ZMod 7211)
      decide
    · change IsUnit ((2 : ZMod 7211) ^ 70 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (205 : ZMod 7211)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 7127) (q := 7129) (by exact lowPrime_7129) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7129) (q := 7151) (by exact lowPrime_7151) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7151) (q := 7159) (by exact lowPrime_7159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7159) (q := 7177) (by exact lowPrime_7177) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7177) (q := 7187) (by exact lowPrime_7187) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7187) (q := 7193) (by exact lowPrime_7193) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7193) (q := 7207) (by exact lowPrime_7207) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7207) (q := 7211) (by exact lowPrime_7211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part03_chain :
    DusartPrimeRowsChain 7127 7211 dusartPrimeRows_6977_7332_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · apply DusartPrimeRowsChain.empty
                  norm_num
