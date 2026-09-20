import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 30 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_5101 : Nat.Prime 5101 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5101 5100 1 6 [2, 2, 3, 5, 5, 17]
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
    · change IsUnit ((6 : ZMod 5101) ^ 2550 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2550 : ZMod 5101)
      decide
    · change IsUnit ((6 : ZMod 5101) ^ 2550 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2550 : ZMod 5101)
      decide
    · change IsUnit ((6 : ZMod 5101) ^ 1700 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2238 : ZMod 5101)
      decide
    · change IsUnit ((6 : ZMod 5101) ^ 1020 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4441 : ZMod 5101)
      decide
    · change IsUnit ((6 : ZMod 5101) ^ 1020 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4441 : ZMod 5101)
      decide
    · change IsUnit ((6 : ZMod 5101) ^ 300 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1688 : ZMod 5101)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5107 : Nat.Prime 5107 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5107 5106 1 2 [2, 3, 23, 37]
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
    · change IsUnit ((2 : ZMod 5107) ^ 2553 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2553 : ZMod 5107)
      decide
    · change IsUnit ((2 : ZMod 5107) ^ 1702 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3508 : ZMod 5107)
      decide
    · change IsUnit ((2 : ZMod 5107) ^ 222 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (298 : ZMod 5107)
      decide
    · change IsUnit ((2 : ZMod 5107) ^ 138 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4488 : ZMod 5107)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5113 : Nat.Prime 5113 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5113 5112 1 19 [2, 2, 2, 3, 3, 71]
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
    · change IsUnit ((19 : ZMod 5113) ^ 2556 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2556 : ZMod 5113)
      decide
    · change IsUnit ((19 : ZMod 5113) ^ 2556 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2556 : ZMod 5113)
      decide
    · change IsUnit ((19 : ZMod 5113) ^ 2556 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2556 : ZMod 5113)
      decide
    · change IsUnit ((19 : ZMod 5113) ^ 1704 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3432 : ZMod 5113)
      decide
    · change IsUnit ((19 : ZMod 5113) ^ 1704 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3432 : ZMod 5113)
      decide
    · change IsUnit ((19 : ZMod 5113) ^ 72 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2372 : ZMod 5113)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5119 : Nat.Prime 5119 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5119 5118 1 3 [2, 3, 853]
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
    · change IsUnit ((3 : ZMod 5119) ^ 2559 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2559 : ZMod 5119)
      decide
    · change IsUnit ((3 : ZMod 5119) ^ 1706 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1145 : ZMod 5119)
      decide
    · change IsUnit ((3 : ZMod 5119) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4451 : ZMod 5119)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5147 : Nat.Prime 5147 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5147 5146 1 2 [2, 31, 83]
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
    · change IsUnit ((2 : ZMod 5147) ^ 2573 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2573 : ZMod 5147)
      decide
    · change IsUnit ((2 : ZMod 5147) ^ 166 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1981 : ZMod 5147)
      decide
    · change IsUnit ((2 : ZMod 5147) ^ 62 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3958 : ZMod 5147)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5153 : Nat.Prime 5153 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5153 5152 1 5 [2, 2, 2, 2, 2, 7, 23]
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
    · change IsUnit ((5 : ZMod 5153) ^ 2576 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2576 : ZMod 5153)
      decide
    · change IsUnit ((5 : ZMod 5153) ^ 2576 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2576 : ZMod 5153)
      decide
    · change IsUnit ((5 : ZMod 5153) ^ 2576 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2576 : ZMod 5153)
      decide
    · change IsUnit ((5 : ZMod 5153) ^ 2576 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2576 : ZMod 5153)
      decide
    · change IsUnit ((5 : ZMod 5153) ^ 2576 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2576 : ZMod 5153)
      decide
    · change IsUnit ((5 : ZMod 5153) ^ 736 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1229 : ZMod 5153)
      decide
    · change IsUnit ((5 : ZMod 5153) ^ 224 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3674 : ZMod 5153)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_5167 : Nat.Prime 5167 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 5167 5166 1 6 [2, 3, 3, 7, 41]
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
    · change IsUnit ((6 : ZMod 5167) ^ 2583 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2583 : ZMod 5167)
      decide
    · change IsUnit ((6 : ZMod 5167) ^ 1722 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (41 : ZMod 5167)
      decide
    · change IsUnit ((6 : ZMod 5167) ^ 1722 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (41 : ZMod 5167)
      decide
    · change IsUnit ((6 : ZMod 5167) ^ 738 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3224 : ZMod 5167)
      decide
    · change IsUnit ((6 : ZMod 5167) ^ 126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1956 : ZMod 5167)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_4919_5166_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_5166 (p := 5099) (q := 5101) (by exact lowPrime_5101) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5101) (q := 5107) (by exact lowPrime_5107) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5107) (q := 5113) (by exact lowPrime_5113) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5113) (q := 5119) (by exact lowPrime_5119) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5119) (q := 5147) (by exact lowPrime_5147) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5147) (q := 5153) (by exact lowPrime_5153) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_5166 (p := 5153) (q := 5167) (by exact lowPrime_5167) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_4919_5166_part04_chain :
    DusartPrimeRowsChain 5099 5167 dusartPrimeRows_4919_5166_part04 := by
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
              · apply DusartPrimeRowsChain.empty
                norm_num
