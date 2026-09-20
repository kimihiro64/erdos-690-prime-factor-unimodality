import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 157 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_13757 : Nat.Prime 13757 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13757 13756 1 2 [2, 2, 19, 181]
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
    · change IsUnit ((2 : ZMod 13757) ^ 6878 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6878 : ZMod 13757)
      decide
    · change IsUnit ((2 : ZMod 13757) ^ 6878 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6878 : ZMod 13757)
      decide
    · change IsUnit ((2 : ZMod 13757) ^ 724 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9457 : ZMod 13757)
      decide
    · change IsUnit ((2 : ZMod 13757) ^ 76 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10755 : ZMod 13757)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13759 : Nat.Prime 13759 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13759 13758 1 6 [2, 3, 2293]
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
    · change IsUnit ((6 : ZMod 13759) ^ 6879 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6879 : ZMod 13759)
      decide
    · change IsUnit ((6 : ZMod 13759) ^ 4586 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4348 : ZMod 13759)
      decide
    · change IsUnit ((6 : ZMod 13759) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1205 : ZMod 13759)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13763 : Nat.Prime 13763 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13763 13762 1 2 [2, 7, 983]
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
    · change IsUnit ((2 : ZMod 13763) ^ 6881 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6881 : ZMod 13763)
      decide
    · change IsUnit ((2 : ZMod 13763) ^ 1966 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5661 : ZMod 13763)
      decide
    · change IsUnit ((2 : ZMod 13763) ^ 14 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3010 : ZMod 13763)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13781 : Nat.Prime 13781 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13781 13780 1 7 [2, 2, 5, 13, 53]
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
    · change IsUnit ((7 : ZMod 13781) ^ 6890 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6890 : ZMod 13781)
      decide
    · change IsUnit ((7 : ZMod 13781) ^ 6890 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6890 : ZMod 13781)
      decide
    · change IsUnit ((7 : ZMod 13781) ^ 2756 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12442 : ZMod 13781)
      decide
    · change IsUnit ((7 : ZMod 13781) ^ 1060 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5898 : ZMod 13781)
      decide
    · change IsUnit ((7 : ZMod 13781) ^ 260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12205 : ZMod 13781)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13789 : Nat.Prime 13789 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13789 13788 1 7 [2, 2, 3, 3, 383]
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
    · change IsUnit ((7 : ZMod 13789) ^ 6894 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6894 : ZMod 13789)
      decide
    · change IsUnit ((7 : ZMod 13789) ^ 6894 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6894 : ZMod 13789)
      decide
    · change IsUnit ((7 : ZMod 13789) ^ 4596 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10001 : ZMod 13789)
      decide
    · change IsUnit ((7 : ZMod 13789) ^ 4596 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10001 : ZMod 13789)
      decide
    · change IsUnit ((7 : ZMod 13789) ^ 36 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3274 : ZMod 13789)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13799 : Nat.Prime 13799 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13799 13798 1 7 [2, 6899]
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
    · change IsUnit ((7 : ZMod 13799) ^ 6899 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6899 : ZMod 13799)
      decide
    · change IsUnit ((7 : ZMod 13799) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7187 : ZMod 13799)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13807 : Nat.Prime 13807 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13807 13806 1 5 [2, 3, 3, 13, 59]
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
    · change IsUnit ((5 : ZMod 13807) ^ 6903 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6903 : ZMod 13807)
      decide
    · change IsUnit ((5 : ZMod 13807) ^ 4602 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9165 : ZMod 13807)
      decide
    · change IsUnit ((5 : ZMod 13807) ^ 4602 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9165 : ZMod 13807)
      decide
    · change IsUnit ((5 : ZMod 13807) ^ 1062 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (717 : ZMod 13807)
      decide
    · change IsUnit ((5 : ZMod 13807) ^ 234 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (519 : ZMod 13807)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_13829 : Nat.Prime 13829 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 13829 13828 1 2 [2, 2, 3457]
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
    · change IsUnit ((2 : ZMod 13829) ^ 6914 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6914 : ZMod 13829)
      decide
    · change IsUnit ((2 : ZMod 13829) ^ 6914 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6914 : ZMod 13829)
      decide
    · change IsUnit ((2 : ZMod 13829) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (922 : ZMod 13829)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_13367_14050_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_14044 (p := 13751) (q := 13757) (by exact lowPrime_13757) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13757) (q := 13759) (by exact lowPrime_13759) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13759) (q := 13763) (by exact lowPrime_13763) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13763) (q := 13781) (by exact lowPrime_13781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13781) (q := 13789) (by exact lowPrime_13789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13789) (q := 13799) (by exact lowPrime_13799) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13799) (q := 13807) (by exact lowPrime_13807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_14044 (p := 13807) (q := 13829) (by exact lowPrime_13829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_13367_14050_part06_chain :
    DusartPrimeRowsChain 13751 13829 dusartPrimeRows_13367_14050_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · norm_num [dusartPrimeRow_of_explicit_14044]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · norm_num [dusartPrimeRow_of_explicit_14044]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · norm_num [dusartPrimeRow_of_explicit_14044]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · norm_num [dusartPrimeRow_of_explicit_14044]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · norm_num [dusartPrimeRow_of_explicit_14044]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · norm_num [dusartPrimeRow_of_explicit_14044]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · norm_num [dusartPrimeRow_of_explicit_14044]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · norm_num [dusartPrimeRow_of_explicit_14044]
                · apply DusartPrimeRowsChain.empty
                  norm_num
