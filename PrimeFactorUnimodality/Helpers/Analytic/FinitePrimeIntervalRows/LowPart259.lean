import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 259 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_18043 : Nat.Prime 18043 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18043 18042 1 2 [2, 3, 31, 97]
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
    · change IsUnit ((2 : ZMod 18043) ^ 9021 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9021 : ZMod 18043)
      decide
    · change IsUnit ((2 : ZMod 18043) ^ 6014 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14098 : ZMod 18043)
      decide
    · change IsUnit ((2 : ZMod 18043) ^ 582 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8385 : ZMod 18043)
      decide
    · change IsUnit ((2 : ZMod 18043) ^ 186 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (860 : ZMod 18043)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18047 : Nat.Prime 18047 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18047 18046 1 5 [2, 7, 1289]
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
    · change IsUnit ((5 : ZMod 18047) ^ 9023 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9023 : ZMod 18047)
      decide
    · change IsUnit ((5 : ZMod 18047) ^ 2578 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17111 : ZMod 18047)
      decide
    · change IsUnit ((5 : ZMod 18047) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (572 : ZMod 18047)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18049 : Nat.Prime 18049 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18049 18048 1 13 [2, 2, 2, 2, 2, 2, 2, 3, 47]
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
    · change IsUnit ((13 : ZMod 18049) ^ 9024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9024 : ZMod 18049)
      decide
    · change IsUnit ((13 : ZMod 18049) ^ 9024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9024 : ZMod 18049)
      decide
    · change IsUnit ((13 : ZMod 18049) ^ 9024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9024 : ZMod 18049)
      decide
    · change IsUnit ((13 : ZMod 18049) ^ 9024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9024 : ZMod 18049)
      decide
    · change IsUnit ((13 : ZMod 18049) ^ 9024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9024 : ZMod 18049)
      decide
    · change IsUnit ((13 : ZMod 18049) ^ 9024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9024 : ZMod 18049)
      decide
    · change IsUnit ((13 : ZMod 18049) ^ 9024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9024 : ZMod 18049)
      decide
    · change IsUnit ((13 : ZMod 18049) ^ 6016 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13119 : ZMod 18049)
      decide
    · change IsUnit ((13 : ZMod 18049) ^ 384 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3873 : ZMod 18049)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18059 : Nat.Prime 18059 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18059 18058 1 2 [2, 9029]
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
    · change IsUnit ((2 : ZMod 18059) ^ 9029 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9029 : ZMod 18059)
      decide
    · change IsUnit ((2 : ZMod 18059) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6020 : ZMod 18059)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18061 : Nat.Prime 18061 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18061 18060 1 6 [2, 2, 3, 5, 7, 43]
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
    · change IsUnit ((6 : ZMod 18061) ^ 9030 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9030 : ZMod 18061)
      decide
    · change IsUnit ((6 : ZMod 18061) ^ 9030 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9030 : ZMod 18061)
      decide
    · change IsUnit ((6 : ZMod 18061) ^ 6020 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11108 : ZMod 18061)
      decide
    · change IsUnit ((6 : ZMod 18061) ^ 3612 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (939 : ZMod 18061)
      decide
    · change IsUnit ((6 : ZMod 18061) ^ 2580 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14576 : ZMod 18061)
      decide
    · change IsUnit ((6 : ZMod 18061) ^ 420 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17703 : ZMod 18061)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18077 : Nat.Prime 18077 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18077 18076 1 2 [2, 2, 4519]
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
    · change IsUnit ((2 : ZMod 18077) ^ 9038 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9038 : ZMod 18077)
      decide
    · change IsUnit ((2 : ZMod 18077) ^ 9038 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9038 : ZMod 18077)
      decide
    · change IsUnit ((2 : ZMod 18077) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8436 : ZMod 18077)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18089 : Nat.Prime 18089 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18089 18088 1 3 [2, 2, 2, 7, 17, 19]
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
    · change IsUnit ((3 : ZMod 18089) ^ 9044 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9044 : ZMod 18089)
      decide
    · change IsUnit ((3 : ZMod 18089) ^ 9044 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9044 : ZMod 18089)
      decide
    · change IsUnit ((3 : ZMod 18089) ^ 9044 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9044 : ZMod 18089)
      decide
    · change IsUnit ((3 : ZMod 18089) ^ 2584 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1018 : ZMod 18089)
      decide
    · change IsUnit ((3 : ZMod 18089) ^ 1064 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9477 : ZMod 18089)
      decide
    · change IsUnit ((3 : ZMod 18089) ^ 952 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7795 : ZMod 18089)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18097 : Nat.Prime 18097 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18097 18096 1 5 [2, 2, 2, 2, 3, 13, 29]
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
    · change IsUnit ((5 : ZMod 18097) ^ 9048 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9048 : ZMod 18097)
      decide
    · change IsUnit ((5 : ZMod 18097) ^ 9048 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9048 : ZMod 18097)
      decide
    · change IsUnit ((5 : ZMod 18097) ^ 9048 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9048 : ZMod 18097)
      decide
    · change IsUnit ((5 : ZMod 18097) ^ 9048 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9048 : ZMod 18097)
      decide
    · change IsUnit ((5 : ZMod 18097) ^ 6032 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14060 : ZMod 18097)
      decide
    · change IsUnit ((5 : ZMod 18097) ^ 1392 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16363 : ZMod 18097)
      decide
    · change IsUnit ((5 : ZMod 18097) ^ 624 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10916 : ZMod 18097)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18041) (q := 18043) (by exact lowPrime_18043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18043) (q := 18047) (by exact lowPrime_18047) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18047) (q := 18049) (by exact lowPrime_18049) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18049) (q := 18059) (by exact lowPrime_18059) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18059) (q := 18061) (by exact lowPrime_18061) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18061) (q := 18077) (by exact lowPrime_18077) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18077) (q := 18089) (by exact lowPrime_18089) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18089) (q := 18097) (by exact lowPrime_18097) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part01_chain :
    DusartPrimeRowsChain 18041 18097 dusartPrimeRows_18041_18958_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num
