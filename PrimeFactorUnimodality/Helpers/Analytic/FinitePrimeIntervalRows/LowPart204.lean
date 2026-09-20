import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 204 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_22031 : Nat.Prime 22031 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22031 22030 1 7 [2, 5, 2203]
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
    · change IsUnit ((7 : ZMod 22031) ^ 11015 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11015 : ZMod 22031)
      decide
    · change IsUnit ((7 : ZMod 22031) ^ 4406 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12806 : ZMod 22031)
      decide
    · change IsUnit ((7 : ZMod 22031) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9093 : ZMod 22031)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22037 : Nat.Prime 22037 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22037 22036 1 2 [2, 2, 7, 787]
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
    · change IsUnit ((2 : ZMod 22037) ^ 11018 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11018 : ZMod 22037)
      decide
    · change IsUnit ((2 : ZMod 22037) ^ 11018 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11018 : ZMod 22037)
      decide
    · change IsUnit ((2 : ZMod 22037) ^ 3148 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (23 : ZMod 22037)
      decide
    · change IsUnit ((2 : ZMod 22037) ^ 28 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16324 : ZMod 22037)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22039 : Nat.Prime 22039 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22039 22038 1 6 [2, 3, 3673]
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
    · change IsUnit ((6 : ZMod 22039) ^ 11019 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11019 : ZMod 22039)
      decide
    · change IsUnit ((6 : ZMod 22039) ^ 7346 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6906 : ZMod 22039)
      decide
    · change IsUnit ((6 : ZMod 22039) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13846 : ZMod 22039)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22051 : Nat.Prime 22051 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22051 22050 1 3 [2, 3, 3, 5, 5, 7, 7]
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
    · change IsUnit ((3 : ZMod 22051) ^ 11025 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11025 : ZMod 22051)
      decide
    · change IsUnit ((3 : ZMod 22051) ^ 7350 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (521 : ZMod 22051)
      decide
    · change IsUnit ((3 : ZMod 22051) ^ 7350 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (521 : ZMod 22051)
      decide
    · change IsUnit ((3 : ZMod 22051) ^ 4410 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (21079 : ZMod 22051)
      decide
    · change IsUnit ((3 : ZMod 22051) ^ 4410 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (21079 : ZMod 22051)
      decide
    · change IsUnit ((3 : ZMod 22051) ^ 3150 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2537 : ZMod 22051)
      decide
    · change IsUnit ((3 : ZMod 22051) ^ 3150 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2537 : ZMod 22051)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22063 : Nat.Prime 22063 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22063 22062 1 5 [2, 3, 3677]
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
    · change IsUnit ((5 : ZMod 22063) ^ 11031 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11031 : ZMod 22063)
      decide
    · change IsUnit ((5 : ZMod 22063) ^ 7354 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2881 : ZMod 22063)
      decide
    · change IsUnit ((5 : ZMod 22063) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14631 : ZMod 22063)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22067 : Nat.Prime 22067 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22067 22066 1 2 [2, 11, 17, 59]
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
    · change IsUnit ((2 : ZMod 22067) ^ 11033 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11033 : ZMod 22067)
      decide
    · change IsUnit ((2 : ZMod 22067) ^ 2006 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8945 : ZMod 22067)
      decide
    · change IsUnit ((2 : ZMod 22067) ^ 1298 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9097 : ZMod 22067)
      decide
    · change IsUnit ((2 : ZMod 22067) ^ 374 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3101 : ZMod 22067)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22073 : Nat.Prime 22073 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22073 22072 1 3 [2, 2, 2, 31, 89]
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
    · change IsUnit ((3 : ZMod 22073) ^ 11036 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11036 : ZMod 22073)
      decide
    · change IsUnit ((3 : ZMod 22073) ^ 11036 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11036 : ZMod 22073)
      decide
    · change IsUnit ((3 : ZMod 22073) ^ 11036 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11036 : ZMod 22073)
      decide
    · change IsUnit ((3 : ZMod 22073) ^ 712 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5739 : ZMod 22073)
      decide
    · change IsUnit ((3 : ZMod 22073) ^ 248 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14510 : ZMod 22073)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_22079 : Nat.Prime 22079 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 22079 22078 1 7 [2, 7, 19, 83]
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
    · change IsUnit ((7 : ZMod 22079) ^ 11039 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11039 : ZMod 22079)
      decide
    · change IsUnit ((7 : ZMod 22079) ^ 3154 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1577 : ZMod 22079)
      decide
    · change IsUnit ((7 : ZMod 22079) ^ 1162 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14255 : ZMod 22079)
      decide
    · change IsUnit ((7 : ZMod 22079) ^ 266 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10687 : ZMod 22079)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_22027_23158_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_23155 (p := 22027) (q := 22031) (by exact lowPrime_22031) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22031) (q := 22037) (by exact lowPrime_22037) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22037) (q := 22039) (by exact lowPrime_22039) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22039) (q := 22051) (by exact lowPrime_22051) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22051) (q := 22063) (by exact lowPrime_22063) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22063) (q := 22067) (by exact lowPrime_22067) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22067) (q := 22073) (by exact lowPrime_22073) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_23155 (p := 22073) (q := 22079) (by exact lowPrime_22079) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_22027_23158_part01_chain :
    DusartPrimeRowsChain 22027 22079 dusartPrimeRows_22027_23158_part01 := by
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
