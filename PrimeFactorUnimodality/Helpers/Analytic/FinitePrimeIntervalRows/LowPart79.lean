import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 79 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_8269 : Nat.Prime 8269 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8269 8268 1 2 [2, 2, 3, 13, 53]
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
    · change IsUnit ((2 : ZMod 8269) ^ 4134 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4134 : ZMod 8269)
      decide
    · change IsUnit ((2 : ZMod 8269) ^ 4134 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4134 : ZMod 8269)
      decide
    · change IsUnit ((2 : ZMod 8269) ^ 2756 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (52 : ZMod 8269)
      decide
    · change IsUnit ((2 : ZMod 8269) ^ 636 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5435 : ZMod 8269)
      decide
    · change IsUnit ((2 : ZMod 8269) ^ 156 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1260 : ZMod 8269)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8273 : Nat.Prime 8273 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8273 8272 1 3 [2, 2, 2, 2, 11, 47]
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
    · change IsUnit ((3 : ZMod 8273) ^ 4136 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4136 : ZMod 8273)
      decide
    · change IsUnit ((3 : ZMod 8273) ^ 4136 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4136 : ZMod 8273)
      decide
    · change IsUnit ((3 : ZMod 8273) ^ 4136 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4136 : ZMod 8273)
      decide
    · change IsUnit ((3 : ZMod 8273) ^ 4136 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4136 : ZMod 8273)
      decide
    · change IsUnit ((3 : ZMod 8273) ^ 752 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3762 : ZMod 8273)
      decide
    · change IsUnit ((3 : ZMod 8273) ^ 176 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6509 : ZMod 8273)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8287 : Nat.Prime 8287 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8287 8286 1 3 [2, 3, 1381]
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
    · change IsUnit ((3 : ZMod 8287) ^ 4143 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4143 : ZMod 8287)
      decide
    · change IsUnit ((3 : ZMod 8287) ^ 2762 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (8097 : ZMod 8287)
      decide
    · change IsUnit ((3 : ZMod 8287) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6386 : ZMod 8287)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8291 : Nat.Prime 8291 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8291 8290 1 2 [2, 5, 829]
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
    · change IsUnit ((2 : ZMod 8291) ^ 4145 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4145 : ZMod 8291)
      decide
    · change IsUnit ((2 : ZMod 8291) ^ 1658 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7547 : ZMod 8291)
      decide
    · change IsUnit ((2 : ZMod 8291) ^ 10 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5114 : ZMod 8291)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8293 : Nat.Prime 8293 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8293 8292 1 2 [2, 2, 3, 691]
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
    · change IsUnit ((2 : ZMod 8293) ^ 4146 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4146 : ZMod 8293)
      decide
    · change IsUnit ((2 : ZMod 8293) ^ 4146 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4146 : ZMod 8293)
      decide
    · change IsUnit ((2 : ZMod 8293) ^ 2764 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (683 : ZMod 8293)
      decide
    · change IsUnit ((2 : ZMod 8293) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5636 : ZMod 8293)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8297 : Nat.Prime 8297 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8297 8296 1 3 [2, 2, 2, 17, 61]
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
    · change IsUnit ((3 : ZMod 8297) ^ 4148 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4148 : ZMod 8297)
      decide
    · change IsUnit ((3 : ZMod 8297) ^ 4148 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4148 : ZMod 8297)
      decide
    · change IsUnit ((3 : ZMod 8297) ^ 4148 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4148 : ZMod 8297)
      decide
    · change IsUnit ((3 : ZMod 8297) ^ 488 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (87 : ZMod 8297)
      decide
    · change IsUnit ((3 : ZMod 8297) ^ 136 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (1311 : ZMod 8297)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8311 : Nat.Prime 8311 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8311 8310 1 3 [2, 3, 5, 277]
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
    · change IsUnit ((3 : ZMod 8311) ^ 4155 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4155 : ZMod 8311)
      decide
    · change IsUnit ((3 : ZMod 8311) ^ 2770 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3192 : ZMod 8311)
      decide
    · change IsUnit ((3 : ZMod 8311) ^ 1662 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5690 : ZMod 8311)
      decide
    · change IsUnit ((3 : ZMod 8311) ^ 30 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4836 : ZMod 8311)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_8317 : Nat.Prime 8317 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 8317 8316 1 6 [2, 2, 3, 3, 3, 7, 11]
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
    · change IsUnit ((6 : ZMod 8317) ^ 4158 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4158 : ZMod 8317)
      decide
    · change IsUnit ((6 : ZMod 8317) ^ 4158 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4158 : ZMod 8317)
      decide
    · change IsUnit ((6 : ZMod 8317) ^ 2772 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2343 : ZMod 8317)
      decide
    · change IsUnit ((6 : ZMod 8317) ^ 2772 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2343 : ZMod 8317)
      decide
    · change IsUnit ((6 : ZMod 8317) ^ 2772 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2343 : ZMod 8317)
      decide
    · change IsUnit ((6 : ZMod 8317) ^ 1188 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2224 : ZMod 8317)
      decide
    · change IsUnit ((6 : ZMod 8317) ^ 756 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (5547 : ZMod 8317)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_8111_8520_part03 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_8518 (p := 8263) (q := 8269) (by exact lowPrime_8269) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8269) (q := 8273) (by exact lowPrime_8273) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8273) (q := 8287) (by exact lowPrime_8287) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8287) (q := 8291) (by exact lowPrime_8291) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8291) (q := 8293) (by exact lowPrime_8293) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8293) (q := 8297) (by exact lowPrime_8297) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8297) (q := 8311) (by exact lowPrime_8311) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_8518 (p := 8311) (q := 8317) (by exact lowPrime_8317) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_8111_8520_part03_chain :
    DusartPrimeRowsChain 8263 8317 dusartPrimeRows_8111_8520_part03 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · norm_num [dusartPrimeRow_of_explicit_8518]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · norm_num [dusartPrimeRow_of_explicit_8518]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · norm_num [dusartPrimeRow_of_explicit_8518]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · norm_num [dusartPrimeRow_of_explicit_8518]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · norm_num [dusartPrimeRow_of_explicit_8518]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · norm_num [dusartPrimeRow_of_explicit_8518]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · norm_num [dusartPrimeRow_of_explicit_8518]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · norm_num [dusartPrimeRow_of_explicit_8518]
                · apply DusartPrimeRowsChain.empty
                  norm_num
