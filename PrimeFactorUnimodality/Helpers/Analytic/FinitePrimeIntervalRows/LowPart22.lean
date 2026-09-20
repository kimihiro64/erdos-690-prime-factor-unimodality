import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 22 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_4639 : Nat.Prime 4639 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4639 4638 1 3 [2, 3, 773]
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
    · change IsUnit ((3 : ZMod 4639) ^ 2319 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2319 : ZMod 4639)
      decide
    · change IsUnit ((3 : ZMod 4639) ^ 1546 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4185 : ZMod 4639)
      decide
    · change IsUnit ((3 : ZMod 4639) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (873 : ZMod 4639)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4643 : Nat.Prime 4643 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4643 4642 1 5 [2, 11, 211]
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
    · change IsUnit ((5 : ZMod 4643) ^ 2321 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2321 : ZMod 4643)
      decide
    · change IsUnit ((5 : ZMod 4643) ^ 422 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3833 : ZMod 4643)
      decide
    · change IsUnit ((5 : ZMod 4643) ^ 22 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1635 : ZMod 4643)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4649 : Nat.Prime 4649 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4649 4648 1 3 [2, 2, 2, 7, 83]
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
    · change IsUnit ((3 : ZMod 4649) ^ 2324 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2324 : ZMod 4649)
      decide
    · change IsUnit ((3 : ZMod 4649) ^ 2324 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2324 : ZMod 4649)
      decide
    · change IsUnit ((3 : ZMod 4649) ^ 2324 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2324 : ZMod 4649)
      decide
    · change IsUnit ((3 : ZMod 4649) ^ 664 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (954 : ZMod 4649)
      decide
    · change IsUnit ((3 : ZMod 4649) ^ 56 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3704 : ZMod 4649)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4651 : Nat.Prime 4651 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4651 4650 1 3 [2, 3, 5, 5, 31]
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
    · change IsUnit ((3 : ZMod 4651) ^ 2325 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2325 : ZMod 4651)
      decide
    · change IsUnit ((3 : ZMod 4651) ^ 1550 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1812 : ZMod 4651)
      decide
    · change IsUnit ((3 : ZMod 4651) ^ 930 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5 : ZMod 4651)
      decide
    · change IsUnit ((3 : ZMod 4651) ^ 930 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5 : ZMod 4651)
      decide
    · change IsUnit ((3 : ZMod 4651) ^ 150 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (995 : ZMod 4651)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4657 : Nat.Prime 4657 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4657 4656 1 15 [2, 2, 2, 2, 3, 97]
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
    · change IsUnit ((15 : ZMod 4657) ^ 2328 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2328 : ZMod 4657)
      decide
    · change IsUnit ((15 : ZMod 4657) ^ 2328 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2328 : ZMod 4657)
      decide
    · change IsUnit ((15 : ZMod 4657) ^ 2328 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2328 : ZMod 4657)
      decide
    · change IsUnit ((15 : ZMod 4657) ^ 2328 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2328 : ZMod 4657)
      decide
    · change IsUnit ((15 : ZMod 4657) ^ 1552 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4334 : ZMod 4657)
      decide
    · change IsUnit ((15 : ZMod 4657) ^ 48 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (863 : ZMod 4657)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4663 : Nat.Prime 4663 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4663 4662 1 3 [2, 3, 3, 7, 37]
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
    · change IsUnit ((3 : ZMod 4663) ^ 2331 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2331 : ZMod 4663)
      decide
    · change IsUnit ((3 : ZMod 4663) ^ 1554 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3965 : ZMod 4663)
      decide
    · change IsUnit ((3 : ZMod 4663) ^ 1554 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3965 : ZMod 4663)
      decide
    · change IsUnit ((3 : ZMod 4663) ^ 666 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4088 : ZMod 4663)
      decide
    · change IsUnit ((3 : ZMod 4663) ^ 126 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1671 : ZMod 4663)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_4673 : Nat.Prime 4673 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 4673 4672 1 3 [2, 2, 2, 2, 2, 2, 73]
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
    · change IsUnit ((3 : ZMod 4673) ^ 2336 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2336 : ZMod 4673)
      decide
    · change IsUnit ((3 : ZMod 4673) ^ 2336 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2336 : ZMod 4673)
      decide
    · change IsUnit ((3 : ZMod 4673) ^ 2336 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2336 : ZMod 4673)
      decide
    · change IsUnit ((3 : ZMod 4673) ^ 2336 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2336 : ZMod 4673)
      decide
    · change IsUnit ((3 : ZMod 4673) ^ 2336 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2336 : ZMod 4673)
      decide
    · change IsUnit ((3 : ZMod 4673) ^ 2336 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2336 : ZMod 4673)
      decide
    · change IsUnit ((3 : ZMod 4673) ^ 64 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1954 : ZMod 4673)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_3803_4672_part13 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_4670 (p := 4637) (q := 4639) (by exact lowPrime_4639) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4639) (q := 4643) (by exact lowPrime_4643) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4643) (q := 4649) (by exact lowPrime_4649) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4649) (q := 4651) (by exact lowPrime_4651) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4651) (q := 4657) (by exact lowPrime_4657) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4657) (q := 4663) (by exact lowPrime_4663) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_4670 (p := 4663) (q := 4673) (by exact lowPrime_4673) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_3803_4672_part13_chain :
    DusartPrimeRowsChain 4637 4673 dusartPrimeRows_3803_4672_part13 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · norm_num [dusartPrimeRow_of_explicit_4670]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · norm_num [dusartPrimeRow_of_explicit_4670]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · norm_num [dusartPrimeRow_of_explicit_4670]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · norm_num [dusartPrimeRow_of_explicit_4670]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · norm_num [dusartPrimeRow_of_explicit_4670]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · norm_num [dusartPrimeRow_of_explicit_4670]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · norm_num [dusartPrimeRow_of_explicit_4670]
              · apply DusartPrimeRowsChain.empty
                norm_num
