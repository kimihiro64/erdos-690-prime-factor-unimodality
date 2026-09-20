import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 234 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_20011 : Nat.Prime 20011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20011 20010 1 12 [2, 3, 5, 23, 29]
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
    · change IsUnit ((12 : ZMod 20011) ^ 10005 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10005 : ZMod 20011)
      decide
    · change IsUnit ((12 : ZMod 20011) ^ 6670 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10183 : ZMod 20011)
      decide
    · change IsUnit ((12 : ZMod 20011) ^ 4002 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4048 : ZMod 20011)
      decide
    · change IsUnit ((12 : ZMod 20011) ^ 870 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6463 : ZMod 20011)
      decide
    · change IsUnit ((12 : ZMod 20011) ^ 690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3840 : ZMod 20011)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20021 : Nat.Prime 20021 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20021 20020 1 3 [2, 2, 5, 7, 11, 13]
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
    · change IsUnit ((3 : ZMod 20021) ^ 10010 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10010 : ZMod 20021)
      decide
    · change IsUnit ((3 : ZMod 20021) ^ 10010 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10010 : ZMod 20021)
      decide
    · change IsUnit ((3 : ZMod 20021) ^ 4004 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1923 : ZMod 20021)
      decide
    · change IsUnit ((3 : ZMod 20021) ^ 2860 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3469 : ZMod 20021)
      decide
    · change IsUnit ((3 : ZMod 20021) ^ 1820 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8566 : ZMod 20021)
      decide
    · change IsUnit ((3 : ZMod 20021) ^ 1540 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6039 : ZMod 20021)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20023 : Nat.Prime 20023 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20023 20022 1 3 [2, 3, 47, 71]
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
    · change IsUnit ((3 : ZMod 20023) ^ 10011 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10011 : ZMod 20023)
      decide
    · change IsUnit ((3 : ZMod 20023) ^ 6674 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6721 : ZMod 20023)
      decide
    · change IsUnit ((3 : ZMod 20023) ^ 426 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5232 : ZMod 20023)
      decide
    · change IsUnit ((3 : ZMod 20023) ^ 282 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8693 : ZMod 20023)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20029 : Nat.Prime 20029 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20029 20028 1 2 [2, 2, 3, 1669]
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
    · change IsUnit ((2 : ZMod 20029) ^ 10014 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10014 : ZMod 20029)
      decide
    · change IsUnit ((2 : ZMod 20029) ^ 10014 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10014 : ZMod 20029)
      decide
    · change IsUnit ((2 : ZMod 20029) ^ 6676 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11111 : ZMod 20029)
      decide
    · change IsUnit ((2 : ZMod 20029) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (494 : ZMod 20029)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20047 : Nat.Prime 20047 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20047 20046 1 3 [2, 3, 13, 257]
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
    · change IsUnit ((3 : ZMod 20047) ^ 10023 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10023 : ZMod 20047)
      decide
    · change IsUnit ((3 : ZMod 20047) ^ 6682 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13194 : ZMod 20047)
      decide
    · change IsUnit ((3 : ZMod 20047) ^ 1542 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9866 : ZMod 20047)
      decide
    · change IsUnit ((3 : ZMod 20047) ^ 78 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16647 : ZMod 20047)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20051 : Nat.Prime 20051 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20051 20050 1 2 [2, 5, 5, 401]
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
    · change IsUnit ((2 : ZMod 20051) ^ 10025 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10025 : ZMod 20051)
      decide
    · change IsUnit ((2 : ZMod 20051) ^ 4010 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4472 : ZMod 20051)
      decide
    · change IsUnit ((2 : ZMod 20051) ^ 4010 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4472 : ZMod 20051)
      decide
    · change IsUnit ((2 : ZMod 20051) ^ 50 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13793 : ZMod 20051)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20063 : Nat.Prime 20063 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20063 20062 1 5 [2, 7, 1433]
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
    · change IsUnit ((5 : ZMod 20063) ^ 10031 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10031 : ZMod 20063)
      decide
    · change IsUnit ((5 : ZMod 20063) ^ 2866 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5916 : ZMod 20063)
      decide
    · change IsUnit ((5 : ZMod 20063) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4856 : ZMod 20063)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20071 : Nat.Prime 20071 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20071 20070 1 3 [2, 3, 3, 5, 223]
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
    · change IsUnit ((3 : ZMod 20071) ^ 10035 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10035 : ZMod 20071)
      decide
    · change IsUnit ((3 : ZMod 20071) ^ 6690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8285 : ZMod 20071)
      decide
    · change IsUnit ((3 : ZMod 20071) ^ 6690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8285 : ZMod 20071)
      decide
    · change IsUnit ((3 : ZMod 20071) ^ 4014 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3700 : ZMod 20071)
      decide
    · change IsUnit ((3 : ZMod 20071) ^ 90 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17940 : ZMod 20071)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part02 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 19997) (q := 20011) (by exact lowPrime_20011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20011) (q := 20021) (by exact lowPrime_20021) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20021) (q := 20023) (by exact lowPrime_20023) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20023) (q := 20029) (by exact lowPrime_20029) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20029) (q := 20047) (by exact lowPrime_20047) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20047) (q := 20051) (by exact lowPrime_20051) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20051) (q := 20063) (by exact lowPrime_20063) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20063) (q := 20071) (by exact lowPrime_20071) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part02_chain :
    DusartPrimeRowsChain 19997 20071 dusartPrimeRows_19937_20958_part02 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · apply DusartPrimeRowsChain.empty
                  norm_num
