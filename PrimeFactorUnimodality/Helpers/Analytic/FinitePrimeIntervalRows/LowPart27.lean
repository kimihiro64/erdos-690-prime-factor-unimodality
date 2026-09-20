import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 27 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_4931 : Nat.Prime 4931 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4931 4930 1 6 [2, 5, 17, 29]
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
    · change IsUnit ((6 : ZMod 4931) ^ 2465 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2465 : ZMod 4931)
      decide
    · change IsUnit ((6 : ZMod 4931) ^ 986 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3280 : ZMod 4931)
      decide
    · change IsUnit ((6 : ZMod 4931) ^ 290 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (583 : ZMod 4931)
      decide
    · change IsUnit ((6 : ZMod 4931) ^ 170 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3570 : ZMod 4931)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4933 : Nat.Prime 4933 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4933 4932 1 2 [2, 2, 3, 3, 137]
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
    · change IsUnit ((2 : ZMod 4933) ^ 2466 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2466 : ZMod 4933)
      decide
    · change IsUnit ((2 : ZMod 4933) ^ 2466 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2466 : ZMod 4933)
      decide
    · change IsUnit ((2 : ZMod 4933) ^ 1644 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4222 : ZMod 4933)
      decide
    · change IsUnit ((2 : ZMod 4933) ^ 1644 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4222 : ZMod 4933)
      decide
    · change IsUnit ((2 : ZMod 4933) ^ 36 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4175 : ZMod 4933)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4937 : Nat.Prime 4937 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4937 4936 1 3 [2, 2, 2, 617]
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
    · change IsUnit ((3 : ZMod 4937) ^ 2468 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2468 : ZMod 4937)
      decide
    · change IsUnit ((3 : ZMod 4937) ^ 2468 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2468 : ZMod 4937)
      decide
    · change IsUnit ((3 : ZMod 4937) ^ 2468 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2468 : ZMod 4937)
      decide
    · change IsUnit ((3 : ZMod 4937) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1089 : ZMod 4937)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4943 : Nat.Prime 4943 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4943 4942 1 7 [2, 7, 353]
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
    · change IsUnit ((7 : ZMod 4943) ^ 2471 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2471 : ZMod 4943)
      decide
    · change IsUnit ((7 : ZMod 4943) ^ 706 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3905 : ZMod 4943)
      decide
    · change IsUnit ((7 : ZMod 4943) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2315 : ZMod 4943)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4951 : Nat.Prime 4951 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4951 4950 1 6 [2, 3, 3, 5, 5, 11]
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
    · change IsUnit ((6 : ZMod 4951) ^ 2475 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2475 : ZMod 4951)
      decide
    · change IsUnit ((6 : ZMod 4951) ^ 1650 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (896 : ZMod 4951)
      decide
    · change IsUnit ((6 : ZMod 4951) ^ 1650 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (896 : ZMod 4951)
      decide
    · change IsUnit ((6 : ZMod 4951) ^ 990 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (660 : ZMod 4951)
      decide
    · change IsUnit ((6 : ZMod 4951) ^ 990 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (660 : ZMod 4951)
      decide
    · change IsUnit ((6 : ZMod 4951) ^ 450 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (320 : ZMod 4951)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4957 : Nat.Prime 4957 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4957 4956 1 2 [2, 2, 3, 7, 59]
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
    · change IsUnit ((2 : ZMod 4957) ^ 2478 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2478 : ZMod 4957)
      decide
    · change IsUnit ((2 : ZMod 4957) ^ 2478 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2478 : ZMod 4957)
      decide
    · change IsUnit ((2 : ZMod 4957) ^ 1652 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4065 : ZMod 4957)
      decide
    · change IsUnit ((2 : ZMod 4957) ^ 708 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4911 : ZMod 4957)
      decide
    · change IsUnit ((2 : ZMod 4957) ^ 84 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (483 : ZMod 4957)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4967 : Nat.Prime 4967 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4967 4966 1 5 [2, 13, 191]
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
    · change IsUnit ((5 : ZMod 4967) ^ 2483 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2483 : ZMod 4967)
      decide
    · change IsUnit ((5 : ZMod 4967) ^ 382 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (755 : ZMod 4967)
      decide
    · change IsUnit ((5 : ZMod 4967) ^ 26 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1551 : ZMod 4967)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4969 : Nat.Prime 4969 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4969 4968 1 11 [2, 2, 2, 3, 3, 3, 23]
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
    · change IsUnit ((11 : ZMod 4969) ^ 2484 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2484 : ZMod 4969)
      decide
    · change IsUnit ((11 : ZMod 4969) ^ 2484 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2484 : ZMod 4969)
      decide
    · change IsUnit ((11 : ZMod 4969) ^ 2484 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2484 : ZMod 4969)
      decide
    · change IsUnit ((11 : ZMod 4969) ^ 1656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1718 : ZMod 4969)
      decide
    · change IsUnit ((11 : ZMod 4969) ^ 1656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1718 : ZMod 4969)
      decide
    · change IsUnit ((11 : ZMod 4969) ^ 1656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1718 : ZMod 4969)
      decide
    · change IsUnit ((11 : ZMod 4969) ^ 216 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4585 : ZMod 4969)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 4919) (q := 4931) (by exact lowPrime_4931) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4931) (q := 4933) (by exact lowPrime_4933) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4933) (q := 4937) (by exact lowPrime_4937) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4937) (q := 4943) (by exact lowPrime_4943) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4943) (q := 4951) (by exact lowPrime_4951) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4951) (q := 4957) (by exact lowPrime_4957) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4957) (q := 4967) (by exact lowPrime_4967) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 4967) (q := 4969) (by exact lowPrime_4969) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part01_chain :
    DusartPrimeRowsChain 4919 4969 dusartPrimeRows_4919_5166_part01 := by
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
