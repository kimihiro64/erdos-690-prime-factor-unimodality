import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 219 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_20963 : Nat.Prime 20963 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20963 20962 1 2 [2, 47, 223]
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
    · change IsUnit ((2 : ZMod 20963) ^ 10481 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10481 : ZMod 20963)
      decide
    · change IsUnit ((2 : ZMod 20963) ^ 446 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2605 : ZMod 20963)
      decide
    · change IsUnit ((2 : ZMod 20963) ^ 94 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13538 : ZMod 20963)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20981 : Nat.Prime 20981 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20981 20980 1 2 [2, 2, 5, 1049]
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
    · change IsUnit ((2 : ZMod 20981) ^ 10490 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10490 : ZMod 20981)
      decide
    · change IsUnit ((2 : ZMod 20981) ^ 10490 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10490 : ZMod 20981)
      decide
    · change IsUnit ((2 : ZMod 20981) ^ 4196 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13824 : ZMod 20981)
      decide
    · change IsUnit ((2 : ZMod 20981) ^ 20 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15283 : ZMod 20981)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20983 : Nat.Prime 20983 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20983 20982 1 3 [2, 3, 13, 269]
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
    · change IsUnit ((3 : ZMod 20983) ^ 10491 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10491 : ZMod 20983)
      decide
    · change IsUnit ((3 : ZMod 20983) ^ 6994 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7423 : ZMod 20983)
      decide
    · change IsUnit ((3 : ZMod 20983) ^ 1614 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9829 : ZMod 20983)
      decide
    · change IsUnit ((3 : ZMod 20983) ^ 78 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16158 : ZMod 20983)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21001 : Nat.Prime 21001 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21001 21000 1 11 [2, 2, 2, 3, 5, 5, 5, 7]
  · norm_num
  · norm_num
  · norm_num
  · intro p hp
    simp at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  · norm_num
  · norm_num
  · rw [← natCast_fastPowMod_eq_pow]
    decide
  · intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change IsUnit ((11 : ZMod 21001) ^ 10500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10500 : ZMod 21001)
      decide
    · change IsUnit ((11 : ZMod 21001) ^ 10500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10500 : ZMod 21001)
      decide
    · change IsUnit ((11 : ZMod 21001) ^ 10500 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10500 : ZMod 21001)
      decide
    · change IsUnit ((11 : ZMod 21001) ^ 7000 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (18609 : ZMod 21001)
      decide
    · change IsUnit ((11 : ZMod 21001) ^ 4200 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14647 : ZMod 21001)
      decide
    · change IsUnit ((11 : ZMod 21001) ^ 4200 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14647 : ZMod 21001)
      decide
    · change IsUnit ((11 : ZMod 21001) ^ 4200 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14647 : ZMod 21001)
      decide
    · change IsUnit ((11 : ZMod 21001) ^ 3000 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (16569 : ZMod 21001)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21011 : Nat.Prime 21011 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21011 21010 1 2 [2, 5, 11, 191]
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
    · change IsUnit ((2 : ZMod 21011) ^ 10505 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10505 : ZMod 21011)
      decide
    · change IsUnit ((2 : ZMod 21011) ^ 4202 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19680 : ZMod 21011)
      decide
    · change IsUnit ((2 : ZMod 21011) ^ 1910 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11131 : ZMod 21011)
      decide
    · change IsUnit ((2 : ZMod 21011) ^ 110 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6142 : ZMod 21011)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21013 : Nat.Prime 21013 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21013 21012 1 2 [2, 2, 3, 17, 103]
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
    · change IsUnit ((2 : ZMod 21013) ^ 10506 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10506 : ZMod 21013)
      decide
    · change IsUnit ((2 : ZMod 21013) ^ 10506 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10506 : ZMod 21013)
      decide
    · change IsUnit ((2 : ZMod 21013) ^ 7004 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11232 : ZMod 21013)
      decide
    · change IsUnit ((2 : ZMod 21013) ^ 1236 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (17301 : ZMod 21013)
      decide
    · change IsUnit ((2 : ZMod 21013) ^ 204 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (14723 : ZMod 21013)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21017 : Nat.Prime 21017 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21017 21016 1 3 [2, 2, 2, 37, 71]
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
    · change IsUnit ((3 : ZMod 21017) ^ 10508 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10508 : ZMod 21017)
      decide
    · change IsUnit ((3 : ZMod 21017) ^ 10508 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10508 : ZMod 21017)
      decide
    · change IsUnit ((3 : ZMod 21017) ^ 10508 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10508 : ZMod 21017)
      decide
    · change IsUnit ((3 : ZMod 21017) ^ 568 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3230 : ZMod 21017)
      decide
    · change IsUnit ((3 : ZMod 21017) ^ 296 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (20654 : ZMod 21017)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_21019 : Nat.Prime 21019 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 21019 21018 1 2 [2, 3, 31, 113]
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
    · change IsUnit ((2 : ZMod 21019) ^ 10509 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10509 : ZMod 21019)
      decide
    · change IsUnit ((2 : ZMod 21019) ^ 7006 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (12441 : ZMod 21019)
      decide
    · change IsUnit ((2 : ZMod 21019) ^ 678 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11386 : ZMod 21019)
      decide
    · change IsUnit ((2 : ZMod 21019) ^ 186 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (612 : ZMod 21019)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_20959_22026_part01 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_22026 (p := 20959) (q := 20963) (by exact lowPrime_20963) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20963) (q := 20981) (by exact lowPrime_20981) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20981) (q := 20983) (by exact lowPrime_20983) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 20983) (q := 21001) (by exact lowPrime_21001) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21001) (q := 21011) (by exact lowPrime_21011) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21011) (q := 21013) (by exact lowPrime_21013) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21013) (q := 21017) (by exact lowPrime_21017) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_22026 (p := 21017) (q := 21019) (by exact lowPrime_21019) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_20959_22026_part01_chain :
    DusartPrimeRowsChain 20959 21019 dusartPrimeRows_20959_22026_part01 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · norm_num [dusartPrimeRow_of_explicit_22026]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · norm_num [dusartPrimeRow_of_explicit_22026]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · norm_num [dusartPrimeRow_of_explicit_22026]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · norm_num [dusartPrimeRow_of_explicit_22026]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · norm_num [dusartPrimeRow_of_explicit_22026]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · norm_num [dusartPrimeRow_of_explicit_22026]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · norm_num [dusartPrimeRow_of_explicit_22026]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · norm_num [dusartPrimeRow_of_explicit_22026]
                · apply DusartPrimeRowsChain.empty
                  norm_num
