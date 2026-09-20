import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 231 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_21871 : Nat.Prime 21871 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21871 21870 1 6 [2, 3, 3, 3, 3, 3, 3, 3, 5]
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
    · change IsUnit ((6 : ZMod 21871) ^ 10935 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10935 : ZMod 21871)
      decide
    · change IsUnit ((6 : ZMod 21871) ^ 7290 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17968 : ZMod 21871)
      decide
    · change IsUnit ((6 : ZMod 21871) ^ 7290 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17968 : ZMod 21871)
      decide
    · change IsUnit ((6 : ZMod 21871) ^ 7290 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17968 : ZMod 21871)
      decide
    · change IsUnit ((6 : ZMod 21871) ^ 7290 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17968 : ZMod 21871)
      decide
    · change IsUnit ((6 : ZMod 21871) ^ 7290 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17968 : ZMod 21871)
      decide
    · change IsUnit ((6 : ZMod 21871) ^ 7290 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17968 : ZMod 21871)
      decide
    · change IsUnit ((6 : ZMod 21871) ^ 7290 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17968 : ZMod 21871)
      decide
    · change IsUnit ((6 : ZMod 21871) ^ 4374 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12548 : ZMod 21871)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21881 : Nat.Prime 21881 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21881 21880 1 3 [2, 2, 2, 5, 547]
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
    · change IsUnit ((3 : ZMod 21881) ^ 10940 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10940 : ZMod 21881)
      decide
    · change IsUnit ((3 : ZMod 21881) ^ 10940 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10940 : ZMod 21881)
      decide
    · change IsUnit ((3 : ZMod 21881) ^ 10940 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10940 : ZMod 21881)
      decide
    · change IsUnit ((3 : ZMod 21881) ^ 4376 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (387 : ZMod 21881)
      decide
    · change IsUnit ((3 : ZMod 21881) ^ 40 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (598 : ZMod 21881)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21893 : Nat.Prime 21893 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21893 21892 1 2 [2, 2, 13, 421]
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
    · change IsUnit ((2 : ZMod 21893) ^ 10946 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10946 : ZMod 21893)
      decide
    · change IsUnit ((2 : ZMod 21893) ^ 10946 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10946 : ZMod 21893)
      decide
    · change IsUnit ((2 : ZMod 21893) ^ 1684 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9950 : ZMod 21893)
      decide
    · change IsUnit ((2 : ZMod 21893) ^ 52 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17863 : ZMod 21893)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21911 : Nat.Prime 21911 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21911 21910 1 13 [2, 5, 7, 313]
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
    · change IsUnit ((13 : ZMod 21911) ^ 10955 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10955 : ZMod 21911)
      decide
    · change IsUnit ((13 : ZMod 21911) ^ 4382 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2413 : ZMod 21911)
      decide
    · change IsUnit ((13 : ZMod 21911) ^ 3130 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6172 : ZMod 21911)
      decide
    · change IsUnit ((13 : ZMod 21911) ^ 70 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5511 : ZMod 21911)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21929 : Nat.Prime 21929 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21929 21928 1 3 [2, 2, 2, 2741]
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
    · change IsUnit ((3 : ZMod 21929) ^ 10964 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10964 : ZMod 21929)
      decide
    · change IsUnit ((3 : ZMod 21929) ^ 10964 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10964 : ZMod 21929)
      decide
    · change IsUnit ((3 : ZMod 21929) ^ 10964 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10964 : ZMod 21929)
      decide
    · change IsUnit ((3 : ZMod 21929) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8795 : ZMod 21929)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21937 : Nat.Prime 21937 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21937 21936 1 7 [2, 2, 2, 2, 3, 457]
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
    · change IsUnit ((7 : ZMod 21937) ^ 10968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10968 : ZMod 21937)
      decide
    · change IsUnit ((7 : ZMod 21937) ^ 10968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10968 : ZMod 21937)
      decide
    · change IsUnit ((7 : ZMod 21937) ^ 10968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10968 : ZMod 21937)
      decide
    · change IsUnit ((7 : ZMod 21937) ^ 10968 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10968 : ZMod 21937)
      decide
    · change IsUnit ((7 : ZMod 21937) ^ 7312 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4404 : ZMod 21937)
      decide
    · change IsUnit ((7 : ZMod 21937) ^ 48 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (20011 : ZMod 21937)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21943 : Nat.Prime 21943 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21943 21942 1 5 [2, 3, 3, 23, 53]
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
    · change IsUnit ((5 : ZMod 21943) ^ 10971 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10971 : ZMod 21943)
      decide
    · change IsUnit ((5 : ZMod 21943) ^ 7314 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3122 : ZMod 21943)
      decide
    · change IsUnit ((5 : ZMod 21943) ^ 7314 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3122 : ZMod 21943)
      decide
    · change IsUnit ((5 : ZMod 21943) ^ 954 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4650 : ZMod 21943)
      decide
    · change IsUnit ((5 : ZMod 21943) ^ 414 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15752 : ZMod 21943)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21961 : Nat.Prime 21961 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21961 21960 1 17 [2, 2, 2, 3, 3, 5, 61]
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
    · change IsUnit ((17 : ZMod 21961) ^ 10980 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10980 : ZMod 21961)
      decide
    · change IsUnit ((17 : ZMod 21961) ^ 10980 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10980 : ZMod 21961)
      decide
    · change IsUnit ((17 : ZMod 21961) ^ 10980 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10980 : ZMod 21961)
      decide
    · change IsUnit ((17 : ZMod 21961) ^ 7320 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9974 : ZMod 21961)
      decide
    · change IsUnit ((17 : ZMod 21961) ^ 7320 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9974 : ZMod 21961)
      decide
    · change IsUnit ((17 : ZMod 21961) ^ 4392 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13413 : ZMod 21961)
      decide
    · change IsUnit ((17 : ZMod 21961) ^ 360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17855 : ZMod 21961)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 21863) (q := 21871) (by exact lowPrime_21871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21871) (q := 21881) (by exact lowPrime_21881) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21881) (q := 21893) (by exact lowPrime_21893) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21893) (q := 21911) (by exact lowPrime_21911) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21911) (q := 21929) (by exact lowPrime_21929) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21929) (q := 21937) (by exact lowPrime_21937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21937) (q := 21943) (by exact lowPrime_21943) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21943) (q := 21961) (by exact lowPrime_21961) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part13_chain :
    DusartPrimeRowsChain 21863 21961 dusartPrimeRows_20959_22026_part13 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num
