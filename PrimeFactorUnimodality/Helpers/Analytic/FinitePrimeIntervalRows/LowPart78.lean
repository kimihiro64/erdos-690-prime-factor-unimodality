import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 78 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_8209 : Nat.Prime 8209 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8209 8208 1 7 [2, 2, 2, 2, 3, 3, 3, 19]
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
    · change IsUnit ((7 : ZMod 8209) ^ 4104 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4104 : ZMod 8209)
      decide
    · change IsUnit ((7 : ZMod 8209) ^ 4104 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4104 : ZMod 8209)
      decide
    · change IsUnit ((7 : ZMod 8209) ^ 4104 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4104 : ZMod 8209)
      decide
    · change IsUnit ((7 : ZMod 8209) ^ 4104 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4104 : ZMod 8209)
      decide
    · change IsUnit ((7 : ZMod 8209) ^ 2736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7120 : ZMod 8209)
      decide
    · change IsUnit ((7 : ZMod 8209) ^ 2736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7120 : ZMod 8209)
      decide
    · change IsUnit ((7 : ZMod 8209) ^ 2736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7120 : ZMod 8209)
      decide
    · change IsUnit ((7 : ZMod 8209) ^ 432 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3087 : ZMod 8209)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8219 : Nat.Prime 8219 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8219 8218 1 2 [2, 7, 587]
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
    · change IsUnit ((2 : ZMod 8219) ^ 4109 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4109 : ZMod 8219)
      decide
    · change IsUnit ((2 : ZMod 8219) ^ 1174 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (261 : ZMod 8219)
      decide
    · change IsUnit ((2 : ZMod 8219) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5828 : ZMod 8219)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8221 : Nat.Prime 8221 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8221 8220 1 2 [2, 2, 3, 5, 137]
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
    · change IsUnit ((2 : ZMod 8221) ^ 4110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4110 : ZMod 8221)
      decide
    · change IsUnit ((2 : ZMod 8221) ^ 4110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4110 : ZMod 8221)
      decide
    · change IsUnit ((2 : ZMod 8221) ^ 2740 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8082 : ZMod 8221)
      decide
    · change IsUnit ((2 : ZMod 8221) ^ 1644 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1189 : ZMod 8221)
      decide
    · change IsUnit ((2 : ZMod 8221) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7376 : ZMod 8221)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8231 : Nat.Prime 8231 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8231 8230 1 11 [2, 5, 823]
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
    · change IsUnit ((11 : ZMod 8231) ^ 4115 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4115 : ZMod 8231)
      decide
    · change IsUnit ((11 : ZMod 8231) ^ 1646 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2645 : ZMod 8231)
      decide
    · change IsUnit ((11 : ZMod 8231) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1546 : ZMod 8231)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8233 : Nat.Prime 8233 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8233 8232 1 10 [2, 2, 2, 3, 7, 7, 7]
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
    · change IsUnit ((10 : ZMod 8233) ^ 4116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4116 : ZMod 8233)
      decide
    · change IsUnit ((10 : ZMod 8233) ^ 4116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4116 : ZMod 8233)
      decide
    · change IsUnit ((10 : ZMod 8233) ^ 4116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4116 : ZMod 8233)
      decide
    · change IsUnit ((10 : ZMod 8233) ^ 2744 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1873 : ZMod 8233)
      decide
    · change IsUnit ((10 : ZMod 8233) ^ 1176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7943 : ZMod 8233)
      decide
    · change IsUnit ((10 : ZMod 8233) ^ 1176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7943 : ZMod 8233)
      decide
    · change IsUnit ((10 : ZMod 8233) ^ 1176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7943 : ZMod 8233)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8237 : Nat.Prime 8237 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8237 8236 1 2 [2, 2, 29, 71]
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
    · change IsUnit ((2 : ZMod 8237) ^ 4118 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4118 : ZMod 8237)
      decide
    · change IsUnit ((2 : ZMod 8237) ^ 4118 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4118 : ZMod 8237)
      decide
    · change IsUnit ((2 : ZMod 8237) ^ 284 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6337 : ZMod 8237)
      decide
    · change IsUnit ((2 : ZMod 8237) ^ 116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5515 : ZMod 8237)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8243 : Nat.Prime 8243 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8243 8242 1 2 [2, 13, 317]
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
    · change IsUnit ((2 : ZMod 8243) ^ 4121 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4121 : ZMod 8243)
      decide
    · change IsUnit ((2 : ZMod 8243) ^ 634 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4637 : ZMod 8243)
      decide
    · change IsUnit ((2 : ZMod 8243) ^ 26 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1563 : ZMod 8243)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8263 : Nat.Prime 8263 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8263 8262 1 3 [2, 3, 3, 3, 3, 3, 17]
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
    · change IsUnit ((3 : ZMod 8263) ^ 4131 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4131 : ZMod 8263)
      decide
    · change IsUnit ((3 : ZMod 8263) ^ 2754 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5428 : ZMod 8263)
      decide
    · change IsUnit ((3 : ZMod 8263) ^ 2754 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5428 : ZMod 8263)
      decide
    · change IsUnit ((3 : ZMod 8263) ^ 2754 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5428 : ZMod 8263)
      decide
    · change IsUnit ((3 : ZMod 8263) ^ 2754 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5428 : ZMod 8263)
      decide
    · change IsUnit ((3 : ZMod 8263) ^ 2754 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5428 : ZMod 8263)
      decide
    · change IsUnit ((3 : ZMod 8263) ^ 486 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7741 : ZMod 8263)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8191) (q := 8209) (by exact lowPrime_8209) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8209) (q := 8219) (by exact lowPrime_8219) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8219) (q := 8221) (by exact lowPrime_8221) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8221) (q := 8231) (by exact lowPrime_8231) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8231) (q := 8233) (by exact lowPrime_8233) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8233) (q := 8237) (by exact lowPrime_8237) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8237) (q := 8243) (by exact lowPrime_8243) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8243) (q := 8263) (by exact lowPrime_8263) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part02_chain :
    DusartPrimeRowsChain 8191 8263 dusartPrimeRows_8111_8520_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num
