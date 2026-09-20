import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 102 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_9781 : Nat.Prime 9781 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9781 9780 1 6 [2, 2, 3, 5, 163]
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
    · change IsUnit ((6 : ZMod 9781) ^ 4890 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4890 : ZMod 9781)
      decide
    · change IsUnit ((6 : ZMod 9781) ^ 4890 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4890 : ZMod 9781)
      decide
    · change IsUnit ((6 : ZMod 9781) ^ 3260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1824 : ZMod 9781)
      decide
    · change IsUnit ((6 : ZMod 9781) ^ 1956 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1602 : ZMod 9781)
      decide
    · change IsUnit ((6 : ZMod 9781) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1085 : ZMod 9781)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9787 : Nat.Prime 9787 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9787 9786 1 3 [2, 3, 7, 233]
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
    · change IsUnit ((3 : ZMod 9787) ^ 4893 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4893 : ZMod 9787)
      decide
    · change IsUnit ((3 : ZMod 9787) ^ 3262 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1010 : ZMod 9787)
      decide
    · change IsUnit ((3 : ZMod 9787) ^ 1398 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4852 : ZMod 9787)
      decide
    · change IsUnit ((3 : ZMod 9787) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2923 : ZMod 9787)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9791 : Nat.Prime 9791 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9791 9790 1 11 [2, 5, 11, 89]
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
    · change IsUnit ((11 : ZMod 9791) ^ 4895 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4895 : ZMod 9791)
      decide
    · change IsUnit ((11 : ZMod 9791) ^ 1958 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2554 : ZMod 9791)
      decide
    · change IsUnit ((11 : ZMod 9791) ^ 890 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3431 : ZMod 9791)
      decide
    · change IsUnit ((11 : ZMod 9791) ^ 110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1704 : ZMod 9791)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9803 : Nat.Prime 9803 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9803 9802 1 2 [2, 13, 13, 29]
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
    · change IsUnit ((2 : ZMod 9803) ^ 4901 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4901 : ZMod 9803)
      decide
    · change IsUnit ((2 : ZMod 9803) ^ 754 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2966 : ZMod 9803)
      decide
    · change IsUnit ((2 : ZMod 9803) ^ 754 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2966 : ZMod 9803)
      decide
    · change IsUnit ((2 : ZMod 9803) ^ 338 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5594 : ZMod 9803)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9811 : Nat.Prime 9811 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9811 9810 1 3 [2, 3, 3, 5, 109]
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
    · change IsUnit ((3 : ZMod 9811) ^ 4905 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4905 : ZMod 9811)
      decide
    · change IsUnit ((3 : ZMod 9811) ^ 3270 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6741 : ZMod 9811)
      decide
    · change IsUnit ((3 : ZMod 9811) ^ 3270 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6741 : ZMod 9811)
      decide
    · change IsUnit ((3 : ZMod 9811) ^ 1962 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (651 : ZMod 9811)
      decide
    · change IsUnit ((3 : ZMod 9811) ^ 90 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8430 : ZMod 9811)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9817 : Nat.Prime 9817 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9817 9816 1 5 [2, 2, 2, 3, 409]
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
    · change IsUnit ((5 : ZMod 9817) ^ 4908 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4908 : ZMod 9817)
      decide
    · change IsUnit ((5 : ZMod 9817) ^ 4908 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4908 : ZMod 9817)
      decide
    · change IsUnit ((5 : ZMod 9817) ^ 4908 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4908 : ZMod 9817)
      decide
    · change IsUnit ((5 : ZMod 9817) ^ 3272 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (318 : ZMod 9817)
      decide
    · change IsUnit ((5 : ZMod 9817) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7256 : ZMod 9817)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9829 : Nat.Prime 9829 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9829 9828 1 10 [2, 2, 3, 3, 3, 7, 13]
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
    · change IsUnit ((10 : ZMod 9829) ^ 4914 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4914 : ZMod 9829)
      decide
    · change IsUnit ((10 : ZMod 9829) ^ 4914 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4914 : ZMod 9829)
      decide
    · change IsUnit ((10 : ZMod 9829) ^ 3276 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9579 : ZMod 9829)
      decide
    · change IsUnit ((10 : ZMod 9829) ^ 3276 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9579 : ZMod 9829)
      decide
    · change IsUnit ((10 : ZMod 9829) ^ 3276 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9579 : ZMod 9829)
      decide
    · change IsUnit ((10 : ZMod 9829) ^ 1404 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7189 : ZMod 9829)
      decide
    · change IsUnit ((10 : ZMod 9829) ^ 756 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5419 : ZMod 9829)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9833 : Nat.Prime 9833 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9833 9832 1 3 [2, 2, 2, 1229]
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
    · change IsUnit ((3 : ZMod 9833) ^ 4916 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4916 : ZMod 9833)
      decide
    · change IsUnit ((3 : ZMod 9833) ^ 4916 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4916 : ZMod 9833)
      decide
    · change IsUnit ((3 : ZMod 9833) ^ 4916 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4916 : ZMod 9833)
      decide
    · change IsUnit ((3 : ZMod 9833) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3512 : ZMod 9833)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part06 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9769) (q := 9781) (by exact lowPrime_9781) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9781) (q := 9787) (by exact lowPrime_9787) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9787) (q := 9791) (by exact lowPrime_9791) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9791) (q := 9803) (by exact lowPrime_9803) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9803) (q := 9811) (by exact lowPrime_9811) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9811) (q := 9817) (by exact lowPrime_9817) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9817) (q := 9829) (by exact lowPrime_9829) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9829) (q := 9833) (by exact lowPrime_9833) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part06_chain :
    DusartPrimeRowsChain 9769 9833 dusartPrimeRows_9419_9900_part06 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · norm_num [dusartPrimeRow_of_explicit_9897]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · norm_num [dusartPrimeRow_of_explicit_9897]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · norm_num [dusartPrimeRow_of_explicit_9897]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · norm_num [dusartPrimeRow_of_explicit_9897]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · norm_num [dusartPrimeRow_of_explicit_9897]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · norm_num [dusartPrimeRow_of_explicit_9897]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · norm_num [dusartPrimeRow_of_explicit_9897]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · norm_num [dusartPrimeRow_of_explicit_9897]
                · apply DusartPrimeRowsChain.empty
                  norm_num
