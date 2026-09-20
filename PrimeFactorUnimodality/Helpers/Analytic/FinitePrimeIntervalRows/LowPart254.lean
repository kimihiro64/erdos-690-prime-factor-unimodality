import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 254 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_19577 : Nat.Prime 19577 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19577 19576 1 3 [2, 2, 2, 2447]
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
    · change IsUnit ((3 : ZMod 19577) ^ 9788 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9788 : ZMod 19577)
      decide
    · change IsUnit ((3 : ZMod 19577) ^ 9788 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9788 : ZMod 19577)
      decide
    · change IsUnit ((3 : ZMod 19577) ^ 9788 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9788 : ZMod 19577)
      decide
    · change IsUnit ((3 : ZMod 19577) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5512 : ZMod 19577)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19583 : Nat.Prime 19583 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19583 19582 1 5 [2, 9791]
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
    · change IsUnit ((5 : ZMod 19583) ^ 9791 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9791 : ZMod 19583)
      decide
    · change IsUnit ((5 : ZMod 19583) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (816 : ZMod 19583)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19597 : Nat.Prime 19597 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19597 19596 1 2 [2, 2, 3, 23, 71]
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
    · change IsUnit ((2 : ZMod 19597) ^ 9798 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9798 : ZMod 19597)
      decide
    · change IsUnit ((2 : ZMod 19597) ^ 9798 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9798 : ZMod 19597)
      decide
    · change IsUnit ((2 : ZMod 19597) ^ 6532 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14890 : ZMod 19597)
      decide
    · change IsUnit ((2 : ZMod 19597) ^ 852 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8114 : ZMod 19597)
      decide
    · change IsUnit ((2 : ZMod 19597) ^ 276 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16613 : ZMod 19597)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19603 : Nat.Prime 19603 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19603 19602 1 2 [2, 3, 3, 3, 3, 11, 11]
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
    · change IsUnit ((2 : ZMod 19603) ^ 9801 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9801 : ZMod 19603)
      decide
    · change IsUnit ((2 : ZMod 19603) ^ 6534 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16312 : ZMod 19603)
      decide
    · change IsUnit ((2 : ZMod 19603) ^ 6534 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16312 : ZMod 19603)
      decide
    · change IsUnit ((2 : ZMod 19603) ^ 6534 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16312 : ZMod 19603)
      decide
    · change IsUnit ((2 : ZMod 19603) ^ 6534 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16312 : ZMod 19603)
      decide
    · change IsUnit ((2 : ZMod 19603) ^ 1782 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5002 : ZMod 19603)
      decide
    · change IsUnit ((2 : ZMod 19603) ^ 1782 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5002 : ZMod 19603)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19609 : Nat.Prime 19609 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19609 19608 1 13 [2, 2, 2, 3, 19, 43]
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
    · change IsUnit ((13 : ZMod 19609) ^ 9804 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9804 : ZMod 19609)
      decide
    · change IsUnit ((13 : ZMod 19609) ^ 9804 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9804 : ZMod 19609)
      decide
    · change IsUnit ((13 : ZMod 19609) ^ 9804 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9804 : ZMod 19609)
      decide
    · change IsUnit ((13 : ZMod 19609) ^ 6536 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (291 : ZMod 19609)
      decide
    · change IsUnit ((13 : ZMod 19609) ^ 1032 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3907 : ZMod 19609)
      decide
    · change IsUnit ((13 : ZMod 19609) ^ 456 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11242 : ZMod 19609)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19661 : Nat.Prime 19661 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19661 19660 1 2 [2, 2, 5, 983]
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
    · change IsUnit ((2 : ZMod 19661) ^ 9830 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9830 : ZMod 19661)
      decide
    · change IsUnit ((2 : ZMod 19661) ^ 9830 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9830 : ZMod 19661)
      decide
    · change IsUnit ((2 : ZMod 19661) ^ 3932 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7394 : ZMod 19661)
      decide
    · change IsUnit ((2 : ZMod 19661) ^ 20 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12920 : ZMod 19661)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19681 : Nat.Prime 19681 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19681 19680 1 11 [2, 2, 2, 2, 2, 3, 5, 41]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((11 : ZMod 19681) ^ 9840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9840 : ZMod 19681)
      decide
    · change IsUnit ((11 : ZMod 19681) ^ 9840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9840 : ZMod 19681)
      decide
    · change IsUnit ((11 : ZMod 19681) ^ 9840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9840 : ZMod 19681)
      decide
    · change IsUnit ((11 : ZMod 19681) ^ 9840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9840 : ZMod 19681)
      decide
    · change IsUnit ((11 : ZMod 19681) ^ 9840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9840 : ZMod 19681)
      decide
    · change IsUnit ((11 : ZMod 19681) ^ 6560 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15239 : ZMod 19681)
      decide
    · change IsUnit ((11 : ZMod 19681) ^ 3936 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16439 : ZMod 19681)
      decide
    · change IsUnit ((11 : ZMod 19681) ^ 480 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10965 : ZMod 19681)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19687 : Nat.Prime 19687 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19687 19686 1 5 [2, 3, 17, 193]
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
    · change IsUnit ((5 : ZMod 19687) ^ 9843 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9843 : ZMod 19687)
      decide
    · change IsUnit ((5 : ZMod 19687) ^ 6562 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4901 : ZMod 19687)
      decide
    · change IsUnit ((5 : ZMod 19687) ^ 1158 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6914 : ZMod 19687)
      decide
    · change IsUnit ((5 : ZMod 19687) ^ 102 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11946 : ZMod 19687)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part09 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19571) (q := 19577) (by exact lowPrime_19577) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19577) (q := 19583) (by exact lowPrime_19583) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19583) (q := 19597) (by exact lowPrime_19597) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19597) (q := 19603) (by exact lowPrime_19603) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19603) (q := 19609) (by exact lowPrime_19609) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19609) (q := 19661) (by exact lowPrime_19661) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19661) (q := 19681) (by exact lowPrime_19681) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19681) (q := 19687) (by exact lowPrime_19687) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part09_chain :
    DusartPrimeRowsChain 19571 19687 dusartPrimeRows_18959_19936_part09 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · norm_num [dusartPrimeRow_of_explicit_19930]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · norm_num [dusartPrimeRow_of_explicit_19930]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · norm_num [dusartPrimeRow_of_explicit_19930]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · norm_num [dusartPrimeRow_of_explicit_19930]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · norm_num [dusartPrimeRow_of_explicit_19930]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · norm_num [dusartPrimeRow_of_explicit_19930]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · norm_num [dusartPrimeRow_of_explicit_19930]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · norm_num [dusartPrimeRow_of_explicit_19930]
                · apply DusartPrimeRowsChain.empty
                  norm_num
