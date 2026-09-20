import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 200 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_16903 : Nat.Prime 16903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16903 16902 1 3 [2, 3, 3, 3, 313]
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
    · change IsUnit ((3 : ZMod 16903) ^ 8451 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8451 : ZMod 16903)
      decide
    · change IsUnit ((3 : ZMod 16903) ^ 5634 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14107 : ZMod 16903)
      decide
    · change IsUnit ((3 : ZMod 16903) ^ 5634 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14107 : ZMod 16903)
      decide
    · change IsUnit ((3 : ZMod 16903) ^ 5634 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14107 : ZMod 16903)
      decide
    · change IsUnit ((3 : ZMod 16903) ^ 54 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2649 : ZMod 16903)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16921 : Nat.Prime 16921 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16921 16920 1 17 [2, 2, 2, 3, 3, 5, 47]
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
    · change IsUnit ((17 : ZMod 16921) ^ 8460 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8460 : ZMod 16921)
      decide
    · change IsUnit ((17 : ZMod 16921) ^ 8460 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8460 : ZMod 16921)
      decide
    · change IsUnit ((17 : ZMod 16921) ^ 8460 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8460 : ZMod 16921)
      decide
    · change IsUnit ((17 : ZMod 16921) ^ 5640 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7089 : ZMod 16921)
      decide
    · change IsUnit ((17 : ZMod 16921) ^ 5640 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7089 : ZMod 16921)
      decide
    · change IsUnit ((17 : ZMod 16921) ^ 3384 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3900 : ZMod 16921)
      decide
    · change IsUnit ((17 : ZMod 16921) ^ 360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8249 : ZMod 16921)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16927 : Nat.Prime 16927 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16927 16926 1 6 [2, 3, 7, 13, 31]
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
    · change IsUnit ((6 : ZMod 16927) ^ 8463 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8463 : ZMod 16927)
      decide
    · change IsUnit ((6 : ZMod 16927) ^ 5642 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6575 : ZMod 16927)
      decide
    · change IsUnit ((6 : ZMod 16927) ^ 2418 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9950 : ZMod 16927)
      decide
    · change IsUnit ((6 : ZMod 16927) ^ 1302 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6954 : ZMod 16927)
      decide
    · change IsUnit ((6 : ZMod 16927) ^ 546 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12642 : ZMod 16927)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16931 : Nat.Prime 16931 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16931 16930 1 2 [2, 5, 1693]
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
    · change IsUnit ((2 : ZMod 16931) ^ 8465 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8465 : ZMod 16931)
      decide
    · change IsUnit ((2 : ZMod 16931) ^ 3386 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6655 : ZMod 16931)
      decide
    · change IsUnit ((2 : ZMod 16931) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14465 : ZMod 16931)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16937 : Nat.Prime 16937 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16937 16936 1 3 [2, 2, 2, 29, 73]
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
    · change IsUnit ((3 : ZMod 16937) ^ 8468 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8468 : ZMod 16937)
      decide
    · change IsUnit ((3 : ZMod 16937) ^ 8468 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8468 : ZMod 16937)
      decide
    · change IsUnit ((3 : ZMod 16937) ^ 8468 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8468 : ZMod 16937)
      decide
    · change IsUnit ((3 : ZMod 16937) ^ 584 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12706 : ZMod 16937)
      decide
    · change IsUnit ((3 : ZMod 16937) ^ 232 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8118 : ZMod 16937)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16943 : Nat.Prime 16943 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16943 16942 1 5 [2, 43, 197]
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
    · change IsUnit ((5 : ZMod 16943) ^ 8471 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8471 : ZMod 16943)
      decide
    · change IsUnit ((5 : ZMod 16943) ^ 394 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16517 : ZMod 16943)
      decide
    · change IsUnit ((5 : ZMod 16943) ^ 86 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13077 : ZMod 16943)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16963 : Nat.Prime 16963 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16963 16962 1 2 [2, 3, 11, 257]
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
    · change IsUnit ((2 : ZMod 16963) ^ 8481 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8481 : ZMod 16963)
      decide
    · change IsUnit ((2 : ZMod 16963) ^ 5654 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16347 : ZMod 16963)
      decide
    · change IsUnit ((2 : ZMod 16963) ^ 1542 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10137 : ZMod 16963)
      decide
    · change IsUnit ((2 : ZMod 16963) ^ 66 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1187 : ZMod 16963)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_16979 : Nat.Prime 16979 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 16979 16978 1 2 [2, 13, 653]
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
    · change IsUnit ((2 : ZMod 16979) ^ 8489 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8489 : ZMod 16979)
      decide
    · change IsUnit ((2 : ZMod 16979) ^ 1306 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2205 : ZMod 16979)
      decide
    · change IsUnit ((2 : ZMod 16979) ^ 26 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4509 : ZMod 16979)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_16319_17158_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_17154 (p := 16901) (q := 16903) (by exact lowPrime_16903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16903) (q := 16921) (by exact lowPrime_16921) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16921) (q := 16927) (by exact lowPrime_16927) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16927) (q := 16931) (by exact lowPrime_16931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16931) (q := 16937) (by exact lowPrime_16937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16937) (q := 16943) (by exact lowPrime_16943) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16943) (q := 16963) (by exact lowPrime_16963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_17154 (p := 16963) (q := 16979) (by exact lowPrime_16979) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_16319_17158_part08_chain :
    DusartPrimeRowsChain 16901 16979 dusartPrimeRows_16319_17158_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · norm_num [dusartPrimeRow_of_explicit_17154]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · norm_num [dusartPrimeRow_of_explicit_17154]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · norm_num [dusartPrimeRow_of_explicit_17154]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · norm_num [dusartPrimeRow_of_explicit_17154]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · norm_num [dusartPrimeRow_of_explicit_17154]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · norm_num [dusartPrimeRow_of_explicit_17154]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · norm_num [dusartPrimeRow_of_explicit_17154]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · norm_num [dusartPrimeRow_of_explicit_17154]
                · apply DusartPrimeRowsChain.empty
                  norm_num
