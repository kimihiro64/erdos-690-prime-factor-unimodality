import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 257 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_19843 : Nat.Prime 19843 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19843 19842 1 19 [2, 3, 3307]
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
    · change IsUnit ((19 : ZMod 19843) ^ 9921 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9921 : ZMod 19843)
      decide
    · change IsUnit ((19 : ZMod 19843) ^ 6614 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15803 : ZMod 19843)
      decide
    · change IsUnit ((19 : ZMod 19843) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15065 : ZMod 19843)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19853 : Nat.Prime 19853 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19853 19852 1 2 [2, 2, 7, 709]
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
    · change IsUnit ((2 : ZMod 19853) ^ 9926 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9926 : ZMod 19853)
      decide
    · change IsUnit ((2 : ZMod 19853) ^ 9926 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9926 : ZMod 19853)
      decide
    · change IsUnit ((2 : ZMod 19853) ^ 2836 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9158 : ZMod 19853)
      decide
    · change IsUnit ((2 : ZMod 19853) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (124 : ZMod 19853)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19861 : Nat.Prime 19861 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19861 19860 1 11 [2, 2, 3, 5, 331]
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
    · change IsUnit ((11 : ZMod 19861) ^ 9930 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9930 : ZMod 19861)
      decide
    · change IsUnit ((11 : ZMod 19861) ^ 9930 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9930 : ZMod 19861)
      decide
    · change IsUnit ((11 : ZMod 19861) ^ 6620 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11143 : ZMod 19861)
      decide
    · change IsUnit ((11 : ZMod 19861) ^ 3972 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6913 : ZMod 19861)
      decide
    · change IsUnit ((11 : ZMod 19861) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2000 : ZMod 19861)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19867 : Nat.Prime 19867 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19867 19866 1 2 [2, 3, 7, 11, 43]
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
    · change IsUnit ((2 : ZMod 19867) ^ 9933 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9933 : ZMod 19867)
      decide
    · change IsUnit ((2 : ZMod 19867) ^ 6622 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14776 : ZMod 19867)
      decide
    · change IsUnit ((2 : ZMod 19867) ^ 2838 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5342 : ZMod 19867)
      decide
    · change IsUnit ((2 : ZMod 19867) ^ 1806 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19534 : ZMod 19867)
      decide
    · change IsUnit ((2 : ZMod 19867) ^ 462 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12416 : ZMod 19867)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19889 : Nat.Prime 19889 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19889 19888 1 3 [2, 2, 2, 2, 11, 113]
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
    · change IsUnit ((3 : ZMod 19889) ^ 9944 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9944 : ZMod 19889)
      decide
    · change IsUnit ((3 : ZMod 19889) ^ 9944 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9944 : ZMod 19889)
      decide
    · change IsUnit ((3 : ZMod 19889) ^ 9944 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9944 : ZMod 19889)
      decide
    · change IsUnit ((3 : ZMod 19889) ^ 9944 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9944 : ZMod 19889)
      decide
    · change IsUnit ((3 : ZMod 19889) ^ 1808 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1630 : ZMod 19889)
      decide
    · change IsUnit ((3 : ZMod 19889) ^ 176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13974 : ZMod 19889)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19891 : Nat.Prime 19891 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19891 19890 1 2 [2, 3, 3, 5, 13, 17]
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
    · change IsUnit ((2 : ZMod 19891) ^ 9945 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9945 : ZMod 19891)
      decide
    · change IsUnit ((2 : ZMod 19891) ^ 6630 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7172 : ZMod 19891)
      decide
    · change IsUnit ((2 : ZMod 19891) ^ 6630 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7172 : ZMod 19891)
      decide
    · change IsUnit ((2 : ZMod 19891) ^ 3978 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19139 : ZMod 19891)
      decide
    · change IsUnit ((2 : ZMod 19891) ^ 1530 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11976 : ZMod 19891)
      decide
    · change IsUnit ((2 : ZMod 19891) ^ 1170 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2694 : ZMod 19891)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19913 : Nat.Prime 19913 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19913 19912 1 3 [2, 2, 2, 19, 131]
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
    · change IsUnit ((3 : ZMod 19913) ^ 9956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9956 : ZMod 19913)
      decide
    · change IsUnit ((3 : ZMod 19913) ^ 9956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9956 : ZMod 19913)
      decide
    · change IsUnit ((3 : ZMod 19913) ^ 9956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9956 : ZMod 19913)
      decide
    · change IsUnit ((3 : ZMod 19913) ^ 1048 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15115 : ZMod 19913)
      decide
    · change IsUnit ((3 : ZMod 19913) ^ 152 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8511 : ZMod 19913)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_19919 : Nat.Prime 19919 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 19919 19918 1 7 [2, 23, 433]
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
    · change IsUnit ((7 : ZMod 19919) ^ 9959 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9959 : ZMod 19919)
      decide
    · change IsUnit ((7 : ZMod 19919) ^ 866 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16088 : ZMod 19919)
      decide
    · change IsUnit ((7 : ZMod 19919) ^ 46 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14882 : ZMod 19919)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18959_19936_part12 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_19930 (p := 19841) (q := 19843) (by exact lowPrime_19843) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19843) (q := 19853) (by exact lowPrime_19853) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19853) (q := 19861) (by exact lowPrime_19861) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19861) (q := 19867) (by exact lowPrime_19867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19867) (q := 19889) (by exact lowPrime_19889) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19889) (q := 19891) (by exact lowPrime_19891) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19891) (q := 19913) (by exact lowPrime_19913) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_19930 (p := 19913) (q := 19919) (by exact lowPrime_19919) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18959_19936_part12_chain :
    DusartPrimeRowsChain 19841 19919 dusartPrimeRows_18959_19936_part12 := by
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
