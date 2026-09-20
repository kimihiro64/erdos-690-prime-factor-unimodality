import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 60 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_6983 : Nat.Prime 6983 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6983 6982 1 5 [2, 3491]
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
    · change IsUnit ((5 : ZMod 6983) ^ 3491 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3491 : ZMod 6983)
      decide
    · change IsUnit ((5 : ZMod 6983) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (291 : ZMod 6983)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6991 : Nat.Prime 6991 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6991 6990 1 6 [2, 3, 5, 233]
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
    · change IsUnit ((6 : ZMod 6991) ^ 3495 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3495 : ZMod 6991)
      decide
    · change IsUnit ((6 : ZMod 6991) ^ 2330 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (460 : ZMod 6991)
      decide
    · change IsUnit ((6 : ZMod 6991) ^ 1398 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1550 : ZMod 6991)
      decide
    · change IsUnit ((6 : ZMod 6991) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5837 : ZMod 6991)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_6997 : Nat.Prime 6997 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 6997 6996 1 5 [2, 2, 3, 11, 53]
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
    · change IsUnit ((5 : ZMod 6997) ^ 3498 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3498 : ZMod 6997)
      decide
    · change IsUnit ((5 : ZMod 6997) ^ 3498 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3498 : ZMod 6997)
      decide
    · change IsUnit ((5 : ZMod 6997) ^ 2332 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (969 : ZMod 6997)
      decide
    · change IsUnit ((5 : ZMod 6997) ^ 636 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3594 : ZMod 6997)
      decide
    · change IsUnit ((5 : ZMod 6997) ^ 132 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1658 : ZMod 6997)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7001 : Nat.Prime 7001 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7001 7000 1 3 [2, 2, 2, 5, 5, 5, 7]
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
    · change IsUnit ((3 : ZMod 7001) ^ 3500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3500 : ZMod 7001)
      decide
    · change IsUnit ((3 : ZMod 7001) ^ 3500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3500 : ZMod 7001)
      decide
    · change IsUnit ((3 : ZMod 7001) ^ 3500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3500 : ZMod 7001)
      decide
    · change IsUnit ((3 : ZMod 7001) ^ 1400 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6077 : ZMod 7001)
      decide
    · change IsUnit ((3 : ZMod 7001) ^ 1400 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6077 : ZMod 7001)
      decide
    · change IsUnit ((3 : ZMod 7001) ^ 1400 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6077 : ZMod 7001)
      decide
    · change IsUnit ((3 : ZMod 7001) ^ 1000 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4721 : ZMod 7001)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7013 : Nat.Prime 7013 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7013 7012 1 2 [2, 2, 1753]
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
    · change IsUnit ((2 : ZMod 7013) ^ 3506 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3506 : ZMod 7013)
      decide
    · change IsUnit ((2 : ZMod 7013) ^ 3506 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3506 : ZMod 7013)
      decide
    · change IsUnit ((2 : ZMod 7013) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6078 : ZMod 7013)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7019 : Nat.Prime 7019 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7019 7018 1 2 [2, 11, 11, 29]
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
    · change IsUnit ((2 : ZMod 7019) ^ 3509 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3509 : ZMod 7019)
      decide
    · change IsUnit ((2 : ZMod 7019) ^ 638 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (607 : ZMod 7019)
      decide
    · change IsUnit ((2 : ZMod 7019) ^ 638 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (607 : ZMod 7019)
      decide
    · change IsUnit ((2 : ZMod 7019) ^ 242 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2965 : ZMod 7019)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7027 : Nat.Prime 7027 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7027 7026 1 2 [2, 3, 1171]
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
    · change IsUnit ((2 : ZMod 7027) ^ 3513 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3513 : ZMod 7027)
      decide
    · change IsUnit ((2 : ZMod 7027) ^ 2342 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (174 : ZMod 7027)
      decide
    · change IsUnit ((2 : ZMod 7027) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5577 : ZMod 7027)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_7039 : Nat.Prime 7039 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 7039 7038 1 3 [2, 3, 3, 17, 23]
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
    · change IsUnit ((3 : ZMod 7039) ^ 3519 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3519 : ZMod 7039)
      decide
    · change IsUnit ((3 : ZMod 7039) ^ 2346 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2245 : ZMod 7039)
      decide
    · change IsUnit ((3 : ZMod 7039) ^ 2346 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2245 : ZMod 7039)
      decide
    · change IsUnit ((3 : ZMod 7039) ^ 414 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3663 : ZMod 7039)
      decide
    · change IsUnit ((3 : ZMod 7039) ^ 306 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6035 : ZMod 7039)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_6977_7332_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_7331 (p := 6977) (q := 6983) (by exact lowPrime_6983) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6983) (q := 6991) (by exact lowPrime_6991) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6991) (q := 6997) (by exact lowPrime_6997) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 6997) (q := 7001) (by exact lowPrime_7001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7001) (q := 7013) (by exact lowPrime_7013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7013) (q := 7019) (by exact lowPrime_7019) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7019) (q := 7027) (by exact lowPrime_7027) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_7331 (p := 7027) (q := 7039) (by exact lowPrime_7039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_6977_7332_part01_chain :
    DusartPrimeRowsChain 6977 7039 dusartPrimeRows_6977_7332_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · norm_num [dusartPrimeRow_of_explicit_7331]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · norm_num [dusartPrimeRow_of_explicit_7331]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · norm_num [dusartPrimeRow_of_explicit_7331]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · norm_num [dusartPrimeRow_of_explicit_7331]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · norm_num [dusartPrimeRow_of_explicit_7331]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · norm_num [dusartPrimeRow_of_explicit_7331]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · norm_num [dusartPrimeRow_of_explicit_7331]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · norm_num [dusartPrimeRow_of_explicit_7331]
                · apply DusartPrimeRowsChain.empty
                  norm_num
