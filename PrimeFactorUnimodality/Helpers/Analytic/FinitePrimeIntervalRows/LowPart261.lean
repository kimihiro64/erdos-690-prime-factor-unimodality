import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 261 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_18181 : Nat.Prime 18181 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18181 18180 1 2 [2, 2, 3, 3, 5, 101]
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
    · change IsUnit ((2 : ZMod 18181) ^ 9090 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9090 : ZMod 18181)
      decide
    · change IsUnit ((2 : ZMod 18181) ^ 9090 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9090 : ZMod 18181)
      decide
    · change IsUnit ((2 : ZMod 18181) ^ 6060 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3852 : ZMod 18181)
      decide
    · change IsUnit ((2 : ZMod 18181) ^ 6060 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3852 : ZMod 18181)
      decide
    · change IsUnit ((2 : ZMod 18181) ^ 3636 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1019 : ZMod 18181)
      decide
    · change IsUnit ((2 : ZMod 18181) ^ 180 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13973 : ZMod 18181)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18191 : Nat.Prime 18191 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18191 18190 1 29 [2, 5, 17, 107]
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
    · change IsUnit ((29 : ZMod 18191) ^ 9095 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9095 : ZMod 18191)
      decide
    · change IsUnit ((29 : ZMod 18191) ^ 3638 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (166 : ZMod 18191)
      decide
    · change IsUnit ((29 : ZMod 18191) ^ 1070 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (960 : ZMod 18191)
      decide
    · change IsUnit ((29 : ZMod 18191) ^ 170 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4925 : ZMod 18191)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18199 : Nat.Prime 18199 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18199 18198 1 11 [2, 3, 3, 3, 337]
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
    · change IsUnit ((11 : ZMod 18199) ^ 9099 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9099 : ZMod 18199)
      decide
    · change IsUnit ((11 : ZMod 18199) ^ 6066 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (339 : ZMod 18199)
      decide
    · change IsUnit ((11 : ZMod 18199) ^ 6066 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (339 : ZMod 18199)
      decide
    · change IsUnit ((11 : ZMod 18199) ^ 6066 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (339 : ZMod 18199)
      decide
    · change IsUnit ((11 : ZMod 18199) ^ 54 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7826 : ZMod 18199)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18211 : Nat.Prime 18211 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18211 18210 1 7 [2, 3, 5, 607]
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
    · change IsUnit ((7 : ZMod 18211) ^ 9105 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9105 : ZMod 18211)
      decide
    · change IsUnit ((7 : ZMod 18211) ^ 6070 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17518 : ZMod 18211)
      decide
    · change IsUnit ((7 : ZMod 18211) ^ 3642 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7603 : ZMod 18211)
      decide
    · change IsUnit ((7 : ZMod 18211) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3102 : ZMod 18211)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18217 : Nat.Prime 18217 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18217 18216 1 7 [2, 2, 2, 3, 3, 11, 23]
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
    · change IsUnit ((7 : ZMod 18217) ^ 9108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9108 : ZMod 18217)
      decide
    · change IsUnit ((7 : ZMod 18217) ^ 9108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9108 : ZMod 18217)
      decide
    · change IsUnit ((7 : ZMod 18217) ^ 9108 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9108 : ZMod 18217)
      decide
    · change IsUnit ((7 : ZMod 18217) ^ 6072 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9345 : ZMod 18217)
      decide
    · change IsUnit ((7 : ZMod 18217) ^ 6072 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9345 : ZMod 18217)
      decide
    · change IsUnit ((7 : ZMod 18217) ^ 1656 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9454 : ZMod 18217)
      decide
    · change IsUnit ((7 : ZMod 18217) ^ 792 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8815 : ZMod 18217)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18223 : Nat.Prime 18223 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18223 18222 1 3 [2, 3, 3037]
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
    · change IsUnit ((3 : ZMod 18223) ^ 9111 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9111 : ZMod 18223)
      decide
    · change IsUnit ((3 : ZMod 18223) ^ 6074 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11424 : ZMod 18223)
      decide
    · change IsUnit ((3 : ZMod 18223) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15845 : ZMod 18223)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18229 : Nat.Prime 18229 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18229 18228 1 2 [2, 2, 3, 7, 7, 31]
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
    · change IsUnit ((2 : ZMod 18229) ^ 9114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9114 : ZMod 18229)
      decide
    · change IsUnit ((2 : ZMod 18229) ^ 9114 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9114 : ZMod 18229)
      decide
    · change IsUnit ((2 : ZMod 18229) ^ 6076 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16974 : ZMod 18229)
      decide
    · change IsUnit ((2 : ZMod 18229) ^ 2604 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17385 : ZMod 18229)
      decide
    · change IsUnit ((2 : ZMod 18229) ^ 2604 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17385 : ZMod 18229)
      decide
    · change IsUnit ((2 : ZMod 18229) ^ 588 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3809 : ZMod 18229)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_18233 : Nat.Prime 18233 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 18233 18232 1 3 [2, 2, 2, 43, 53]
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
    · change IsUnit ((3 : ZMod 18233) ^ 9116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9116 : ZMod 18233)
      decide
    · change IsUnit ((3 : ZMod 18233) ^ 9116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9116 : ZMod 18233)
      decide
    · change IsUnit ((3 : ZMod 18233) ^ 9116 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9116 : ZMod 18233)
      decide
    · change IsUnit ((3 : ZMod 18233) ^ 424 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13150 : ZMod 18233)
      decide
    · change IsUnit ((3 : ZMod 18233) ^ 344 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (438 : ZMod 18233)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_18041_18958_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_18958 (p := 18169) (q := 18181) (by exact lowPrime_18181) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18181) (q := 18191) (by exact lowPrime_18191) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18191) (q := 18199) (by exact lowPrime_18199) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18199) (q := 18211) (by exact lowPrime_18211) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18211) (q := 18217) (by exact lowPrime_18217) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18217) (q := 18223) (by exact lowPrime_18223) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18223) (q := 18229) (by exact lowPrime_18229) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_18958 (p := 18229) (q := 18233) (by exact lowPrime_18233) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_18041_18958_part03_chain :
    DusartPrimeRowsChain 18169 18233 dusartPrimeRows_18041_18958_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · norm_num [dusartPrimeRow_of_explicit_18958]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · norm_num [dusartPrimeRow_of_explicit_18958]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · norm_num [dusartPrimeRow_of_explicit_18958]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · norm_num [dusartPrimeRow_of_explicit_18958]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · norm_num [dusartPrimeRow_of_explicit_18958]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · norm_num [dusartPrimeRow_of_explicit_18958]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · norm_num [dusartPrimeRow_of_explicit_18958]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · norm_num [dusartPrimeRow_of_explicit_18958]
                · apply DusartPrimeRowsChain.empty
                  norm_num
