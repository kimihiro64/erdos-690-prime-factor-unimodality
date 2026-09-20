import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 133 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_12071 : Nat.Prime 12071 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12071 12070 1 11 [2, 5, 17, 71]
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
    · change IsUnit ((11 : ZMod 12071) ^ 6035 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6035 : ZMod 12071)
      decide
    · change IsUnit ((11 : ZMod 12071) ^ 2414 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11856 : ZMod 12071)
      decide
    · change IsUnit ((11 : ZMod 12071) ^ 710 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3067 : ZMod 12071)
      decide
    · change IsUnit ((11 : ZMod 12071) ^ 170 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6470 : ZMod 12071)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12073 : Nat.Prime 12073 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12073 12072 1 7 [2, 2, 2, 3, 503]
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
    · change IsUnit ((7 : ZMod 12073) ^ 6036 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6036 : ZMod 12073)
      decide
    · change IsUnit ((7 : ZMod 12073) ^ 6036 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6036 : ZMod 12073)
      decide
    · change IsUnit ((7 : ZMod 12073) ^ 6036 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6036 : ZMod 12073)
      decide
    · change IsUnit ((7 : ZMod 12073) ^ 4024 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8805 : ZMod 12073)
      decide
    · change IsUnit ((7 : ZMod 12073) ^ 24 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11308 : ZMod 12073)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_12097 : Nat.Prime 12097 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 12097 12096 1 5 [2, 2, 2, 2, 2, 2, 3, 3, 3, 7]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((5 : ZMod 12097) ^ 6048 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6048 : ZMod 12097)
      decide
    · change IsUnit ((5 : ZMod 12097) ^ 6048 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6048 : ZMod 12097)
      decide
    · change IsUnit ((5 : ZMod 12097) ^ 6048 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6048 : ZMod 12097)
      decide
    · change IsUnit ((5 : ZMod 12097) ^ 6048 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6048 : ZMod 12097)
      decide
    · change IsUnit ((5 : ZMod 12097) ^ 6048 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6048 : ZMod 12097)
      decide
    · change IsUnit ((5 : ZMod 12097) ^ 6048 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6048 : ZMod 12097)
      decide
    · change IsUnit ((5 : ZMod 12097) ^ 4032 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12033 : ZMod 12097)
      decide
    · change IsUnit ((5 : ZMod 12097) ^ 4032 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12033 : ZMod 12097)
      decide
    · change IsUnit ((5 : ZMod 12097) ^ 4032 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12033 : ZMod 12097)
      decide
    · change IsUnit ((5 : ZMod 12097) ^ 1728 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7462 : ZMod 12097)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_11503_12096_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_12088 (p := 12049) (q := 12071) (by exact lowPrime_12071) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12071) (q := 12073) (by exact lowPrime_12073) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_12088 (p := 12073) (q := 12097) (by exact lowPrime_12097) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_11503_12096_part08_chain :
    DusartPrimeRowsChain 12049 12097 dusartPrimeRows_11503_12096_part08 := by
  apply DusartPrimeRowsChain.cons
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
