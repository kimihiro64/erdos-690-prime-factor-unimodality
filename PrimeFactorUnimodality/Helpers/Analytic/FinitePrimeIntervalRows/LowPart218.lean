import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 218 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_23099 : Nat.Prime 23099 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23099 23098 1 2 [2, 11549]
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
    · change IsUnit ((2 : ZMod 23099) ^ 11549 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11549 : ZMod 23099)
      decide
    · change IsUnit ((2 : ZMod 23099) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7700 : ZMod 23099)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_23117 : Nat.Prime 23117 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23117 23116 1 2 [2, 2, 5779]
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
    · change IsUnit ((2 : ZMod 23117) ^ 11558 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11558 : ZMod 23117)
      decide
    · change IsUnit ((2 : ZMod 23117) ^ 11558 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11558 : ZMod 23117)
      decide
    · change IsUnit ((2 : ZMod 23117) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10788 : ZMod 23117)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_23131 : Nat.Prime 23131 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23131 23130 1 3 [2, 3, 3, 5, 257]
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
    · change IsUnit ((3 : ZMod 23131) ^ 11565 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11565 : ZMod 23131)
      decide
    · change IsUnit ((3 : ZMod 23131) ^ 7710 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1293 : ZMod 23131)
      decide
    · change IsUnit ((3 : ZMod 23131) ^ 7710 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1293 : ZMod 23131)
      decide
    · change IsUnit ((3 : ZMod 23131) ^ 4626 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19702 : ZMod 23131)
      decide
    · change IsUnit ((3 : ZMod 23131) ^ 90 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5462 : ZMod 23131)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_23143 : Nat.Prime 23143 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23143 23142 1 5 [2, 3, 7, 19, 29]
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
    · change IsUnit ((5 : ZMod 23143) ^ 11571 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11571 : ZMod 23143)
      decide
    · change IsUnit ((5 : ZMod 23143) ^ 7714 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2510 : ZMod 23143)
      decide
    · change IsUnit ((5 : ZMod 23143) ^ 3306 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4097 : ZMod 23143)
      decide
    · change IsUnit ((5 : ZMod 23143) ^ 1218 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6881 : ZMod 23143)
      decide
    · change IsUnit ((5 : ZMod 23143) ^ 798 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11025 : ZMod 23143)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_23159 : Nat.Prime 23159 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 23159 23158 1 11 [2, 11579]
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
    · change IsUnit ((11 : ZMod 23159) ^ 11579 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11579 : ZMod 23159)
      decide
    · change IsUnit ((11 : ZMod 23159) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (193 : ZMod 23159)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part15 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 23087) (q := 23099) (by exact lowPrime_23099) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23099) (q := 23117) (by exact lowPrime_23117) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23117) (q := 23131) (by exact lowPrime_23131) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23131) (q := 23143) (by exact lowPrime_23143) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 23143) (q := 23159) (by exact lowPrime_23159) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part15_chain :
    DusartPrimeRowsChain 23087 23159 dusartPrimeRows_22027_23158_part15 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · norm_num [dusartPrimeRow_of_explicit_23155]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · norm_num [dusartPrimeRow_of_explicit_23155]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · norm_num [dusartPrimeRow_of_explicit_23155]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · norm_num [dusartPrimeRow_of_explicit_23155]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · norm_num [dusartPrimeRow_of_explicit_23155]
          · apply DusartPrimeRowsChain.empty
            norm_num
