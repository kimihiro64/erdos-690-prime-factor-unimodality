import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 143 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_12721 : Nat.Prime 12721 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12721 12720 1 13 [2, 2, 2, 2, 3, 5, 53]
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
    · change IsUnit ((13 : ZMod 12721) ^ 6360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6360 : ZMod 12721)
      decide
    · change IsUnit ((13 : ZMod 12721) ^ 6360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6360 : ZMod 12721)
      decide
    · change IsUnit ((13 : ZMod 12721) ^ 6360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6360 : ZMod 12721)
      decide
    · change IsUnit ((13 : ZMod 12721) ^ 6360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6360 : ZMod 12721)
      decide
    · change IsUnit ((13 : ZMod 12721) ^ 4240 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11077 : ZMod 12721)
      decide
    · change IsUnit ((13 : ZMod 12721) ^ 2544 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (409 : ZMod 12721)
      decide
    · change IsUnit ((13 : ZMod 12721) ^ 240 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6892 : ZMod 12721)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12739 : Nat.Prime 12739 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12739 12738 1 2 [2, 3, 11, 193]
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
    · change IsUnit ((2 : ZMod 12739) ^ 6369 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6369 : ZMod 12739)
      decide
    · change IsUnit ((2 : ZMod 12739) ^ 4246 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2384 : ZMod 12739)
      decide
    · change IsUnit ((2 : ZMod 12739) ^ 1158 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5470 : ZMod 12739)
      decide
    · change IsUnit ((2 : ZMod 12739) ^ 66 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4199 : ZMod 12739)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12743 : Nat.Prime 12743 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12743 12742 1 5 [2, 23, 277]
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
    · change IsUnit ((5 : ZMod 12743) ^ 6371 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6371 : ZMod 12743)
      decide
    · change IsUnit ((5 : ZMod 12743) ^ 554 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11691 : ZMod 12743)
      decide
    · change IsUnit ((5 : ZMod 12743) ^ 46 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8739 : ZMod 12743)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12757 : Nat.Prime 12757 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12757 12756 1 2 [2, 2, 3, 1063]
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
    · change IsUnit ((2 : ZMod 12757) ^ 6378 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6378 : ZMod 12757)
      decide
    · change IsUnit ((2 : ZMod 12757) ^ 6378 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6378 : ZMod 12757)
      decide
    · change IsUnit ((2 : ZMod 12757) ^ 4252 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9293 : ZMod 12757)
      decide
    · change IsUnit ((2 : ZMod 12757) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8838 : ZMod 12757)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12763 : Nat.Prime 12763 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12763 12762 1 2 [2, 3, 3, 709]
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
    · change IsUnit ((2 : ZMod 12763) ^ 6381 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6381 : ZMod 12763)
      decide
    · change IsUnit ((2 : ZMod 12763) ^ 4254 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7497 : ZMod 12763)
      decide
    · change IsUnit ((2 : ZMod 12763) ^ 4254 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7497 : ZMod 12763)
      decide
    · change IsUnit ((2 : ZMod 12763) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3792 : ZMod 12763)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12781 : Nat.Prime 12781 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12781 12780 1 2 [2, 2, 3, 3, 5, 71]
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
    · change IsUnit ((2 : ZMod 12781) ^ 6390 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6390 : ZMod 12781)
      decide
    · change IsUnit ((2 : ZMod 12781) ^ 6390 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6390 : ZMod 12781)
      decide
    · change IsUnit ((2 : ZMod 12781) ^ 4260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1074 : ZMod 12781)
      decide
    · change IsUnit ((2 : ZMod 12781) ^ 4260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1074 : ZMod 12781)
      decide
    · change IsUnit ((2 : ZMod 12781) ^ 2556 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8861 : ZMod 12781)
      decide
    · change IsUnit ((2 : ZMod 12781) ^ 180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10809 : ZMod 12781)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12791 : Nat.Prime 12791 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12791 12790 1 7 [2, 5, 1279]
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
    · change IsUnit ((7 : ZMod 12791) ^ 6395 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6395 : ZMod 12791)
      decide
    · change IsUnit ((7 : ZMod 12791) ^ 2558 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (131 : ZMod 12791)
      decide
    · change IsUnit ((7 : ZMod 12791) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7219 : ZMod 12791)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12799 : Nat.Prime 12799 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12799 12798 1 13 [2, 3, 3, 3, 3, 79]
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
    · change IsUnit ((13 : ZMod 12799) ^ 6399 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6399 : ZMod 12799)
      decide
    · change IsUnit ((13 : ZMod 12799) ^ 4266 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7726 : ZMod 12799)
      decide
    · change IsUnit ((13 : ZMod 12799) ^ 4266 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7726 : ZMod 12799)
      decide
    · change IsUnit ((13 : ZMod 12799) ^ 4266 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7726 : ZMod 12799)
      decide
    · change IsUnit ((13 : ZMod 12799) ^ 4266 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7726 : ZMod 12799)
      decide
    · change IsUnit ((13 : ZMod 12799) ^ 162 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4348 : ZMod 12799)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_12713_13366_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_13359 (p := 12713) (q := 12721) (by exact lowPrime_12721) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12721) (q := 12739) (by exact lowPrime_12739) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12739) (q := 12743) (by exact lowPrime_12743) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12743) (q := 12757) (by exact lowPrime_12757) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12757) (q := 12763) (by exact lowPrime_12763) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12763) (q := 12781) (by exact lowPrime_12781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12781) (q := 12791) (by exact lowPrime_12791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_13359 (p := 12791) (q := 12799) (by exact lowPrime_12799) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_12713_13366_part01_chain :
    DusartPrimeRowsChain 12713 12799 dusartPrimeRows_12713_13366_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · norm_num [dusartPrimeRow_of_explicit_13359]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · norm_num [dusartPrimeRow_of_explicit_13359]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · norm_num [dusartPrimeRow_of_explicit_13359]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · norm_num [dusartPrimeRow_of_explicit_13359]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_13359]
          · norm_num [dusartPrimeRow_of_explicit_13359]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_13359]
            · norm_num [dusartPrimeRow_of_explicit_13359]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_13359]
              · norm_num [dusartPrimeRow_of_explicit_13359]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_13359]
                · norm_num [dusartPrimeRow_of_explicit_13359]
                · apply DusartPrimeRowsChain.empty
                  norm_num
