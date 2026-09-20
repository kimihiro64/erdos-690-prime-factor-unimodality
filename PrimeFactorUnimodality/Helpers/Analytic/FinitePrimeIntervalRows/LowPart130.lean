import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 130 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_11839 : Nat.Prime 11839 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11839 11838 1 3 [2, 3, 1973]
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
    · change IsUnit ((3 : ZMod 11839) ^ 5919 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5919 : ZMod 11839)
      decide
    · change IsUnit ((3 : ZMod 11839) ^ 3946 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11612 : ZMod 11839)
      decide
    · change IsUnit ((3 : ZMod 11839) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7562 : ZMod 11839)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11863 : Nat.Prime 11863 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11863 11862 1 3 [2, 3, 3, 659]
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
    · change IsUnit ((3 : ZMod 11863) ^ 5931 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5931 : ZMod 11863)
      decide
    · change IsUnit ((3 : ZMod 11863) ^ 3954 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5029 : ZMod 11863)
      decide
    · change IsUnit ((3 : ZMod 11863) ^ 3954 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5029 : ZMod 11863)
      decide
    · change IsUnit ((3 : ZMod 11863) ^ 18 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3413 : ZMod 11863)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11867 : Nat.Prime 11867 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11867 11866 1 2 [2, 17, 349]
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
    · change IsUnit ((2 : ZMod 11867) ^ 5933 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5933 : ZMod 11867)
      decide
    · change IsUnit ((2 : ZMod 11867) ^ 698 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9315 : ZMod 11867)
      decide
    · change IsUnit ((2 : ZMod 11867) ^ 34 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10568 : ZMod 11867)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11887 : Nat.Prime 11887 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11887 11886 1 3 [2, 3, 7, 283]
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
    · change IsUnit ((3 : ZMod 11887) ^ 5943 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5943 : ZMod 11887)
      decide
    · change IsUnit ((3 : ZMod 11887) ^ 3962 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5473 : ZMod 11887)
      decide
    · change IsUnit ((3 : ZMod 11887) ^ 1698 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5365 : ZMod 11887)
      decide
    · change IsUnit ((3 : ZMod 11887) ^ 42 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8152 : ZMod 11887)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11897 : Nat.Prime 11897 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11897 11896 1 3 [2, 2, 2, 1487]
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
    · change IsUnit ((3 : ZMod 11897) ^ 5948 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5948 : ZMod 11897)
      decide
    · change IsUnit ((3 : ZMod 11897) ^ 5948 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5948 : ZMod 11897)
      decide
    · change IsUnit ((3 : ZMod 11897) ^ 5948 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5948 : ZMod 11897)
      decide
    · change IsUnit ((3 : ZMod 11897) ^ 8 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3930 : ZMod 11897)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11903 : Nat.Prime 11903 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11903 11902 1 5 [2, 11, 541]
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
    · change IsUnit ((5 : ZMod 11903) ^ 5951 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5951 : ZMod 11903)
      decide
    · change IsUnit ((5 : ZMod 11903) ^ 1082 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5835 : ZMod 11903)
      decide
    · change IsUnit ((5 : ZMod 11903) ^ 22 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9109 : ZMod 11903)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11909 : Nat.Prime 11909 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11909 11908 1 2 [2, 2, 13, 229]
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
    · change IsUnit ((2 : ZMod 11909) ^ 5954 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5954 : ZMod 11909)
      decide
    · change IsUnit ((2 : ZMod 11909) ^ 5954 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5954 : ZMod 11909)
      decide
    · change IsUnit ((2 : ZMod 11909) ^ 916 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7002 : ZMod 11909)
      decide
    · change IsUnit ((2 : ZMod 11909) ^ 52 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7695 : ZMod 11909)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11923 : Nat.Prime 11923 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11923 11922 1 5 [2, 3, 1987]
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
    · change IsUnit ((5 : ZMod 11923) ^ 5961 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5961 : ZMod 11923)
      decide
    · change IsUnit ((5 : ZMod 11923) ^ 3974 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10440 : ZMod 11923)
      decide
    · change IsUnit ((5 : ZMod 11923) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3795 : ZMod 11923)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part05 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11833) (q := 11839) (by exact lowPrime_11839) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11839) (q := 11863) (by exact lowPrime_11863) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11863) (q := 11867) (by exact lowPrime_11867) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11867) (q := 11887) (by exact lowPrime_11887) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11887) (q := 11897) (by exact lowPrime_11897) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11897) (q := 11903) (by exact lowPrime_11903) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11903) (q := 11909) (by exact lowPrime_11909) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11909) (q := 11923) (by exact lowPrime_11923) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part05_chain :
    DusartPrimeRowsChain 11833 11923 dusartPrimeRows_11503_12096_part05 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · norm_num [dusartPrimeRow_of_explicit_12088]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · norm_num [dusartPrimeRow_of_explicit_12088]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · norm_num [dusartPrimeRow_of_explicit_12088]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · norm_num [dusartPrimeRow_of_explicit_12088]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · norm_num [dusartPrimeRow_of_explicit_12088]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · norm_num [dusartPrimeRow_of_explicit_12088]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · norm_num [dusartPrimeRow_of_explicit_12088]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · norm_num [dusartPrimeRow_of_explicit_12088]
                · apply DusartPrimeRowsChain.empty
                  norm_num
