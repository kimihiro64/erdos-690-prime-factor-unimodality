import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 103 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_9839 : Nat.Prime 9839 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9839 9838 1 7 [2, 4919]
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
    · change IsUnit ((7 : ZMod 9839) ^ 4919 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4919 : ZMod 9839)
      decide
    · change IsUnit ((7 : ZMod 9839) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (205 : ZMod 9839)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9851 : Nat.Prime 9851 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9851 9850 1 2 [2, 5, 5, 197]
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
    · change IsUnit ((2 : ZMod 9851) ^ 4925 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4925 : ZMod 9851)
      decide
    · change IsUnit ((2 : ZMod 9851) ^ 1970 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8629 : ZMod 9851)
      decide
    · change IsUnit ((2 : ZMod 9851) ^ 1970 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8629 : ZMod 9851)
      decide
    · change IsUnit ((2 : ZMod 9851) ^ 50 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3882 : ZMod 9851)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9857 : Nat.Prime 9857 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9857 9856 1 5 [2, 2, 2, 2, 2, 2, 2, 7, 11]
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
    · change IsUnit ((5 : ZMod 9857) ^ 4928 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4928 : ZMod 9857)
      decide
    · change IsUnit ((5 : ZMod 9857) ^ 4928 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4928 : ZMod 9857)
      decide
    · change IsUnit ((5 : ZMod 9857) ^ 4928 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4928 : ZMod 9857)
      decide
    · change IsUnit ((5 : ZMod 9857) ^ 4928 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4928 : ZMod 9857)
      decide
    · change IsUnit ((5 : ZMod 9857) ^ 4928 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4928 : ZMod 9857)
      decide
    · change IsUnit ((5 : ZMod 9857) ^ 4928 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4928 : ZMod 9857)
      decide
    · change IsUnit ((5 : ZMod 9857) ^ 4928 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4928 : ZMod 9857)
      decide
    · change IsUnit ((5 : ZMod 9857) ^ 1408 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19 : ZMod 9857)
      decide
    · change IsUnit ((5 : ZMod 9857) ^ 896 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1245 : ZMod 9857)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9859 : Nat.Prime 9859 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9859 9858 1 2 [2, 3, 31, 53]
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
    · change IsUnit ((2 : ZMod 9859) ^ 4929 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4929 : ZMod 9859)
      decide
    · change IsUnit ((2 : ZMod 9859) ^ 3286 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1583 : ZMod 9859)
      decide
    · change IsUnit ((2 : ZMod 9859) ^ 318 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3176 : ZMod 9859)
      decide
    · change IsUnit ((2 : ZMod 9859) ^ 186 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (534 : ZMod 9859)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9871 : Nat.Prime 9871 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9871 9870 1 3 [2, 3, 5, 7, 47]
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
    · change IsUnit ((3 : ZMod 9871) ^ 4935 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4935 : ZMod 9871)
      decide
    · change IsUnit ((3 : ZMod 9871) ^ 3290 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3507 : ZMod 9871)
      decide
    · change IsUnit ((3 : ZMod 9871) ^ 1974 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3318 : ZMod 9871)
      decide
    · change IsUnit ((3 : ZMod 9871) ^ 1410 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6932 : ZMod 9871)
      decide
    · change IsUnit ((3 : ZMod 9871) ^ 210 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5909 : ZMod 9871)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9883 : Nat.Prime 9883 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9883 9882 1 2 [2, 3, 3, 3, 3, 61]
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
    · change IsUnit ((2 : ZMod 9883) ^ 4941 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4941 : ZMod 9883)
      decide
    · change IsUnit ((2 : ZMod 9883) ^ 3294 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9037 : ZMod 9883)
      decide
    · change IsUnit ((2 : ZMod 9883) ^ 3294 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9037 : ZMod 9883)
      decide
    · change IsUnit ((2 : ZMod 9883) ^ 3294 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9037 : ZMod 9883)
      decide
    · change IsUnit ((2 : ZMod 9883) ^ 3294 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9037 : ZMod 9883)
      decide
    · change IsUnit ((2 : ZMod 9883) ^ 162 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6434 : ZMod 9883)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9887 : Nat.Prime 9887 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9887 9886 1 5 [2, 4943]
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
    · change IsUnit ((5 : ZMod 9887) ^ 4943 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4943 : ZMod 9887)
      decide
    · change IsUnit ((5 : ZMod 9887) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (412 : ZMod 9887)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_9901 : Nat.Prime 9901 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 9901 9900 1 2 [2, 2, 3, 3, 5, 5, 11]
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
    · change IsUnit ((2 : ZMod 9901) ^ 4950 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4950 : ZMod 9901)
      decide
    · change IsUnit ((2 : ZMod 9901) ^ 4950 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4950 : ZMod 9901)
      decide
    · change IsUnit ((2 : ZMod 9901) ^ 3300 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6567 : ZMod 9901)
      decide
    · change IsUnit ((2 : ZMod 9901) ^ 3300 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6567 : ZMod 9901)
      decide
    · change IsUnit ((2 : ZMod 9901) ^ 1980 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4084 : ZMod 9901)
      decide
    · change IsUnit ((2 : ZMod 9901) ^ 1980 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4084 : ZMod 9901)
      decide
    · change IsUnit ((2 : ZMod 9901) ^ 900 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4839 : ZMod 9901)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_9419_9900_part07 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_9897 (p := 9833) (q := 9839) (by exact lowPrime_9839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9839) (q := 9851) (by exact lowPrime_9851) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9851) (q := 9857) (by exact lowPrime_9857) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9857) (q := 9859) (by exact lowPrime_9859) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9859) (q := 9871) (by exact lowPrime_9871) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9871) (q := 9883) (by exact lowPrime_9883) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9883) (q := 9887) (by exact lowPrime_9887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_9897 (p := 9887) (q := 9901) (by exact lowPrime_9901) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_9419_9900_part07_chain :
    DusartPrimeRowsChain 9833 9901 dusartPrimeRows_9419_9900_part07 := by
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
