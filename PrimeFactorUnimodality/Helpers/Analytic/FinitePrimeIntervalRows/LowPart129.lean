import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 129 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_11789 : Nat.Prime 11789 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11789 11788 1 2 [2, 2, 7, 421]
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
    · change IsUnit ((2 : ZMod 11789) ^ 5894 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5894 : ZMod 11789)
      decide
    · change IsUnit ((2 : ZMod 11789) ^ 5894 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5894 : ZMod 11789)
      decide
    · change IsUnit ((2 : ZMod 11789) ^ 1684 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1837 : ZMod 11789)
      decide
    · change IsUnit ((2 : ZMod 11789) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9274 : ZMod 11789)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11801 : Nat.Prime 11801 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11801 11800 1 3 [2, 2, 2, 5, 5, 59]
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
    · change IsUnit ((3 : ZMod 11801) ^ 5900 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5900 : ZMod 11801)
      decide
    · change IsUnit ((3 : ZMod 11801) ^ 5900 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5900 : ZMod 11801)
      decide
    · change IsUnit ((3 : ZMod 11801) ^ 5900 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5900 : ZMod 11801)
      decide
    · change IsUnit ((3 : ZMod 11801) ^ 2360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (51 : ZMod 11801)
      decide
    · change IsUnit ((3 : ZMod 11801) ^ 2360 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (51 : ZMod 11801)
      decide
    · change IsUnit ((3 : ZMod 11801) ^ 200 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3077 : ZMod 11801)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11807 : Nat.Prime 11807 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11807 11806 1 5 [2, 5903]
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
    · change IsUnit ((5 : ZMod 11807) ^ 5903 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5903 : ZMod 11807)
      decide
    · change IsUnit ((5 : ZMod 11807) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (492 : ZMod 11807)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11813 : Nat.Prime 11813 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11813 11812 1 2 [2, 2, 2953]
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
    · change IsUnit ((2 : ZMod 11813) ^ 5906 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5906 : ZMod 11813)
      decide
    · change IsUnit ((2 : ZMod 11813) ^ 5906 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5906 : ZMod 11813)
      decide
    · change IsUnit ((2 : ZMod 11813) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10238 : ZMod 11813)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11821 : Nat.Prime 11821 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11821 11820 1 2 [2, 2, 3, 5, 197]
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
    · change IsUnit ((2 : ZMod 11821) ^ 5910 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5910 : ZMod 11821)
      decide
    · change IsUnit ((2 : ZMod 11821) ^ 5910 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5910 : ZMod 11821)
      decide
    · change IsUnit ((2 : ZMod 11821) ^ 3940 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11471 : ZMod 11821)
      decide
    · change IsUnit ((2 : ZMod 11821) ^ 2364 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1566 : ZMod 11821)
      decide
    · change IsUnit ((2 : ZMod 11821) ^ 60 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2941 : ZMod 11821)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11827 : Nat.Prime 11827 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11827 11826 1 2 [2, 3, 3, 3, 3, 73]
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
    · change IsUnit ((2 : ZMod 11827) ^ 5913 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5913 : ZMod 11827)
      decide
    · change IsUnit ((2 : ZMod 11827) ^ 3942 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9131 : ZMod 11827)
      decide
    · change IsUnit ((2 : ZMod 11827) ^ 3942 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9131 : ZMod 11827)
      decide
    · change IsUnit ((2 : ZMod 11827) ^ 3942 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9131 : ZMod 11827)
      decide
    · change IsUnit ((2 : ZMod 11827) ^ 3942 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9131 : ZMod 11827)
      decide
    · change IsUnit ((2 : ZMod 11827) ^ 162 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3225 : ZMod 11827)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11831 : Nat.Prime 11831 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11831 11830 1 7 [2, 5, 7, 13, 13]
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
    · change IsUnit ((7 : ZMod 11831) ^ 5915 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5915 : ZMod 11831)
      decide
    · change IsUnit ((7 : ZMod 11831) ^ 2366 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3558 : ZMod 11831)
      decide
    · change IsUnit ((7 : ZMod 11831) ^ 1690 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3933 : ZMod 11831)
      decide
    · change IsUnit ((7 : ZMod 11831) ^ 910 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3417 : ZMod 11831)
      decide
    · change IsUnit ((7 : ZMod 11831) ^ 910 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3417 : ZMod 11831)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_11833 : Nat.Prime 11833 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 11833 11832 1 5 [2, 2, 2, 3, 17, 29]
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
    · change IsUnit ((5 : ZMod 11833) ^ 5916 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5916 : ZMod 11833)
      decide
    · change IsUnit ((5 : ZMod 11833) ^ 5916 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5916 : ZMod 11833)
      decide
    · change IsUnit ((5 : ZMod 11833) ^ 5916 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5916 : ZMod 11833)
      decide
    · change IsUnit ((5 : ZMod 11833) ^ 3944 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (872 : ZMod 11833)
      decide
    · change IsUnit ((5 : ZMod 11833) ^ 696 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11138 : ZMod 11833)
      decide
    · change IsUnit ((5 : ZMod 11833) ^ 408 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11064 : ZMod 11833)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part04 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 11783) (q := 11789) (by exact lowPrime_11789) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11789) (q := 11801) (by exact lowPrime_11801) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11801) (q := 11807) (by exact lowPrime_11807) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11807) (q := 11813) (by exact lowPrime_11813) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11813) (q := 11821) (by exact lowPrime_11821) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11821) (q := 11827) (by exact lowPrime_11827) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11827) (q := 11831) (by exact lowPrime_11831) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 11831) (q := 11833) (by exact lowPrime_11833) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part04_chain :
    DusartPrimeRowsChain 11783 11833 dusartPrimeRows_11503_12096_part04 := by
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
