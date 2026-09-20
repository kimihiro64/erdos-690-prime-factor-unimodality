import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 132 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_11981 : Nat.Prime 11981 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11981 11980 1 2 [2, 2, 5, 599]
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
    · change IsUnit ((2 : ZMod 11981) ^ 5990 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5990 : ZMod 11981)
      decide
    · change IsUnit ((2 : ZMod 11981) ^ 5990 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5990 : ZMod 11981)
      decide
    · change IsUnit ((2 : ZMod 11981) ^ 2396 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2157 : ZMod 11981)
      decide
    · change IsUnit ((2 : ZMod 11981) ^ 20 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5877 : ZMod 11981)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11987 : Nat.Prime 11987 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11987 11986 1 2 [2, 13, 461]
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
    · change IsUnit ((2 : ZMod 11987) ^ 5993 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5993 : ZMod 11987)
      decide
    · change IsUnit ((2 : ZMod 11987) ^ 922 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3607 : ZMod 11987)
      decide
    · change IsUnit ((2 : ZMod 11987) ^ 26 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9482 : ZMod 11987)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12007 : Nat.Prime 12007 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12007 12006 1 13 [2, 3, 3, 23, 29]
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
    · change IsUnit ((13 : ZMod 12007) ^ 6003 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6003 : ZMod 12007)
      decide
    · change IsUnit ((13 : ZMod 12007) ^ 4002 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11403 : ZMod 12007)
      decide
    · change IsUnit ((13 : ZMod 12007) ^ 4002 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11403 : ZMod 12007)
      decide
    · change IsUnit ((13 : ZMod 12007) ^ 522 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9904 : ZMod 12007)
      decide
    · change IsUnit ((13 : ZMod 12007) ^ 414 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11898 : ZMod 12007)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12011 : Nat.Prime 12011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12011 12010 1 2 [2, 5, 1201]
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
    · change IsUnit ((2 : ZMod 12011) ^ 6005 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6005 : ZMod 12011)
      decide
    · change IsUnit ((2 : ZMod 12011) ^ 2402 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1640 : ZMod 12011)
      decide
    · change IsUnit ((2 : ZMod 12011) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1949 : ZMod 12011)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12037 : Nat.Prime 12037 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12037 12036 1 5 [2, 2, 3, 17, 59]
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
    · change IsUnit ((5 : ZMod 12037) ^ 6018 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6018 : ZMod 12037)
      decide
    · change IsUnit ((5 : ZMod 12037) ^ 6018 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6018 : ZMod 12037)
      decide
    · change IsUnit ((5 : ZMod 12037) ^ 4012 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4443 : ZMod 12037)
      decide
    · change IsUnit ((5 : ZMod 12037) ^ 708 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3487 : ZMod 12037)
      decide
    · change IsUnit ((5 : ZMod 12037) ^ 204 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7037 : ZMod 12037)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12041 : Nat.Prime 12041 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12041 12040 1 3 [2, 2, 2, 5, 7, 43]
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
    · change IsUnit ((3 : ZMod 12041) ^ 6020 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6020 : ZMod 12041)
      decide
    · change IsUnit ((3 : ZMod 12041) ^ 6020 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6020 : ZMod 12041)
      decide
    · change IsUnit ((3 : ZMod 12041) ^ 6020 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6020 : ZMod 12041)
      decide
    · change IsUnit ((3 : ZMod 12041) ^ 2408 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1005 : ZMod 12041)
      decide
    · change IsUnit ((3 : ZMod 12041) ^ 1720 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1759 : ZMod 12041)
      decide
    · change IsUnit ((3 : ZMod 12041) ^ 280 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7076 : ZMod 12041)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12043 : Nat.Prime 12043 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12043 12042 1 2 [2, 3, 3, 3, 223]
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
    · change IsUnit ((2 : ZMod 12043) ^ 6021 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6021 : ZMod 12043)
      decide
    · change IsUnit ((2 : ZMod 12043) ^ 4014 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1054 : ZMod 12043)
      decide
    · change IsUnit ((2 : ZMod 12043) ^ 4014 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1054 : ZMod 12043)
      decide
    · change IsUnit ((2 : ZMod 12043) ^ 4014 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1054 : ZMod 12043)
      decide
    · change IsUnit ((2 : ZMod 12043) ^ 54 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (230 : ZMod 12043)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12049 : Nat.Prime 12049 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12049 12048 1 13 [2, 2, 2, 2, 3, 251]
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
    · change IsUnit ((13 : ZMod 12049) ^ 6024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6024 : ZMod 12049)
      decide
    · change IsUnit ((13 : ZMod 12049) ^ 6024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6024 : ZMod 12049)
      decide
    · change IsUnit ((13 : ZMod 12049) ^ 6024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6024 : ZMod 12049)
      decide
    · change IsUnit ((13 : ZMod 12049) ^ 6024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6024 : ZMod 12049)
      decide
    · change IsUnit ((13 : ZMod 12049) ^ 4016 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11820 : ZMod 12049)
      decide
    · change IsUnit ((13 : ZMod 12049) ^ 48 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11284 : ZMod 12049)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11971) (q := 11981) (by exact lowPrime_11981) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11981) (q := 11987) (by exact lowPrime_11987) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11987) (q := 12007) (by exact lowPrime_12007) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12007) (q := 12011) (by exact lowPrime_12011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12011) (q := 12037) (by exact lowPrime_12037) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12037) (q := 12041) (by exact lowPrime_12041) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12041) (q := 12043) (by exact lowPrime_12043) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12043) (q := 12049) (by exact lowPrime_12049) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part07_chain :
    DusartPrimeRowsChain 11971 12049 dusartPrimeRows_11503_12096_part07 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · apply DusartPrimeRowsChain.empty
                  norm_num
