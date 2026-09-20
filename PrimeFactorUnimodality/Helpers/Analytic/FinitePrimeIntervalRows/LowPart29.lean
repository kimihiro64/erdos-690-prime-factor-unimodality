import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 29 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_5023 : Nat.Prime 5023 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5023 5022 1 3 [2, 3, 3, 3, 3, 31]
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
    · change IsUnit ((3 : ZMod 5023) ^ 2511 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2511 : ZMod 5023)
      decide
    · change IsUnit ((3 : ZMod 5023) ^ 1674 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1356 : ZMod 5023)
      decide
    · change IsUnit ((3 : ZMod 5023) ^ 1674 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1356 : ZMod 5023)
      decide
    · change IsUnit ((3 : ZMod 5023) ^ 1674 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1356 : ZMod 5023)
      decide
    · change IsUnit ((3 : ZMod 5023) ^ 1674 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1356 : ZMod 5023)
      decide
    · change IsUnit ((3 : ZMod 5023) ^ 162 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4048 : ZMod 5023)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5039 : Nat.Prime 5039 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5039 5038 1 11 [2, 11, 229]
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
    · change IsUnit ((11 : ZMod 5039) ^ 2519 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2519 : ZMod 5039)
      decide
    · change IsUnit ((11 : ZMod 5039) ^ 458 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3953 : ZMod 5039)
      decide
    · change IsUnit ((11 : ZMod 5039) ^ 22 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (874 : ZMod 5039)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5051 : Nat.Prime 5051 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5051 5050 1 2 [2, 5, 5, 101]
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
    · change IsUnit ((2 : ZMod 5051) ^ 2525 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2525 : ZMod 5051)
      decide
    · change IsUnit ((2 : ZMod 5051) ^ 1010 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3446 : ZMod 5051)
      decide
    · change IsUnit ((2 : ZMod 5051) ^ 1010 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3446 : ZMod 5051)
      decide
    · change IsUnit ((2 : ZMod 5051) ^ 50 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2703 : ZMod 5051)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5059 : Nat.Prime 5059 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5059 5058 1 2 [2, 3, 3, 281]
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
    · change IsUnit ((2 : ZMod 5059) ^ 2529 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2529 : ZMod 5059)
      decide
    · change IsUnit ((2 : ZMod 5059) ^ 1686 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (637 : ZMod 5059)
      decide
    · change IsUnit ((2 : ZMod 5059) ^ 1686 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (637 : ZMod 5059)
      decide
    · change IsUnit ((2 : ZMod 5059) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3905 : ZMod 5059)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5077 : Nat.Prime 5077 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5077 5076 1 2 [2, 2, 3, 3, 3, 47]
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
    · change IsUnit ((2 : ZMod 5077) ^ 2538 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2538 : ZMod 5077)
      decide
    · change IsUnit ((2 : ZMod 5077) ^ 2538 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2538 : ZMod 5077)
      decide
    · change IsUnit ((2 : ZMod 5077) ^ 1692 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2235 : ZMod 5077)
      decide
    · change IsUnit ((2 : ZMod 5077) ^ 1692 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2235 : ZMod 5077)
      decide
    · change IsUnit ((2 : ZMod 5077) ^ 1692 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2235 : ZMod 5077)
      decide
    · change IsUnit ((2 : ZMod 5077) ^ 108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3509 : ZMod 5077)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5081 : Nat.Prime 5081 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5081 5080 1 3 [2, 2, 2, 5, 127]
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
    · change IsUnit ((3 : ZMod 5081) ^ 2540 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2540 : ZMod 5081)
      decide
    · change IsUnit ((3 : ZMod 5081) ^ 2540 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2540 : ZMod 5081)
      decide
    · change IsUnit ((3 : ZMod 5081) ^ 2540 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2540 : ZMod 5081)
      decide
    · change IsUnit ((3 : ZMod 5081) ^ 1016 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2336 : ZMod 5081)
      decide
    · change IsUnit ((3 : ZMod 5081) ^ 40 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2006 : ZMod 5081)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5087 : Nat.Prime 5087 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5087 5086 1 5 [2, 2543]
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
    · change IsUnit ((5 : ZMod 5087) ^ 2543 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2543 : ZMod 5087)
      decide
    · change IsUnit ((5 : ZMod 5087) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (212 : ZMod 5087)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5099 : Nat.Prime 5099 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5099 5098 1 2 [2, 2549]
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
    · change IsUnit ((2 : ZMod 5099) ^ 2549 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2549 : ZMod 5099)
      decide
    · change IsUnit ((2 : ZMod 5099) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1700 : ZMod 5099)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 5021) (q := 5023) (by exact lowPrime_5023) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5023) (q := 5039) (by exact lowPrime_5039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5039) (q := 5051) (by exact lowPrime_5051) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5051) (q := 5059) (by exact lowPrime_5059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5059) (q := 5077) (by exact lowPrime_5077) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5077) (q := 5081) (by exact lowPrime_5081) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5081) (q := 5087) (by exact lowPrime_5087) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5087) (q := 5099) (by exact lowPrime_5099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part03_chain :
    DusartPrimeRowsChain 5021 5099 dusartPrimeRows_4919_5166_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · norm_num [dusartPrimeRow_of_explicit_5166]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · norm_num [dusartPrimeRow_of_explicit_5166]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · norm_num [dusartPrimeRow_of_explicit_5166]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · norm_num [dusartPrimeRow_of_explicit_5166]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · norm_num [dusartPrimeRow_of_explicit_5166]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · norm_num [dusartPrimeRow_of_explicit_5166]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · norm_num [dusartPrimeRow_of_explicit_5166]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · norm_num [dusartPrimeRow_of_explicit_5166]
                · apply DusartPrimeRowsChain.empty
                  norm_num
