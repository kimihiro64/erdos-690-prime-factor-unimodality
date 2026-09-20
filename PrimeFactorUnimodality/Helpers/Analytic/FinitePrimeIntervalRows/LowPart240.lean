import PrimeFactorUnimodality.Helpers.Analytic.FinitePrimeIntervalRows.LowBase

set_option autoImplicit false
set_option maxRecDepth 100000

/-! # Lower finite Dusart prefix chunk 240 -/

namespace PrimeFactorUnimodality

noncomputable section
set_option maxHeartbeats 20000000 in
theorem lowPrime_20477 : Nat.Prime 20477 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20477 20476 1 2 [2, 2, 5119]
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
    · change IsUnit ((2 : ZMod 20477) ^ 10238 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10238 : ZMod 20477)
      decide
    · change IsUnit ((2 : ZMod 20477) ^ 10238 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10238 : ZMod 20477)
      decide
    · change IsUnit ((2 : ZMod 20477) ^ 4 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (9556 : ZMod 20477)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20479 : Nat.Prime 20479 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20479 20478 1 3 [2, 3, 3413]
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
    · change IsUnit ((3 : ZMod 20479) ^ 10239 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10239 : ZMod 20479)
      decide
    · change IsUnit ((3 : ZMod 20479) ^ 6826 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (4355 : ZMod 20479)
      decide
    · change IsUnit ((3 : ZMod 20479) ^ 6 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19832 : ZMod 20479)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20483 : Nat.Prime 20483 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20483 20482 1 5 [2, 7, 7, 11, 19]
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
    · change IsUnit ((5 : ZMod 20483) ^ 10241 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10241 : ZMod 20483)
      decide
    · change IsUnit ((5 : ZMod 20483) ^ 2926 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3178 : ZMod 20483)
      decide
    · change IsUnit ((5 : ZMod 20483) ^ 2926 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (3178 : ZMod 20483)
      decide
    · change IsUnit ((5 : ZMod 20483) ^ 1862 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13475 : ZMod 20483)
      decide
    · change IsUnit ((5 : ZMod 20483) ^ 1078 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (13169 : ZMod 20483)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20507 : Nat.Prime 20507 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20507 20506 1 2 [2, 10253]
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
    · change IsUnit ((2 : ZMod 20507) ^ 10253 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10253 : ZMod 20507)
      decide
    · change IsUnit ((2 : ZMod 20507) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (6836 : ZMod 20507)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20509 : Nat.Prime 20509 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20509 20508 1 2 [2, 2, 3, 1709]
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
    · change IsUnit ((2 : ZMod 20509) ^ 10254 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10254 : ZMod 20509)
      decide
    · change IsUnit ((2 : ZMod 20509) ^ 10254 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10254 : ZMod 20509)
      decide
    · change IsUnit ((2 : ZMod 20509) ^ 6836 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (2154 : ZMod 20509)
      decide
    · change IsUnit ((2 : ZMod 20509) ^ 12 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15080 : ZMod 20509)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20521 : Nat.Prime 20521 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20521 20520 1 11 [2, 2, 2, 3, 3, 3, 5, 19]
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
    · change IsUnit ((11 : ZMod 20521) ^ 10260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10260 : ZMod 20521)
      decide
    · change IsUnit ((11 : ZMod 20521) ^ 10260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10260 : ZMod 20521)
      decide
    · change IsUnit ((11 : ZMod 20521) ^ 10260 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10260 : ZMod 20521)
      decide
    · change IsUnit ((11 : ZMod 20521) ^ 6840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7012 : ZMod 20521)
      decide
    · change IsUnit ((11 : ZMod 20521) ^ 6840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7012 : ZMod 20521)
      decide
    · change IsUnit ((11 : ZMod 20521) ^ 6840 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7012 : ZMod 20521)
      decide
    · change IsUnit ((11 : ZMod 20521) ^ 4104 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (15971 : ZMod 20521)
      decide
    · change IsUnit ((11 : ZMod 20521) ^ 1080 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11290 : ZMod 20521)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20533 : Nat.Prime 20533 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20533 20532 1 2 [2, 2, 3, 29, 59]
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
    · change IsUnit ((2 : ZMod 20533) ^ 10266 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10266 : ZMod 20533)
      decide
    · change IsUnit ((2 : ZMod 20533) ^ 10266 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10266 : ZMod 20533)
      decide
    · change IsUnit ((2 : ZMod 20533) ^ 6844 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (19990 : ZMod 20533)
      decide
    · change IsUnit ((2 : ZMod 20533) ^ 708 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (11583 : ZMod 20533)
      decide
    · change IsUnit ((2 : ZMod 20533) ^ 348 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (7719 : ZMod 20533)
      decide
  · norm_num

set_option maxHeartbeats 20000000 in
theorem lowPrime_20543 : Nat.Prime 20543 := by
  apply Nat.prime_of_pocklington_factor_of_prime_factors 20543 20542 1 5 [2, 10271]
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
    · change IsUnit ((5 : ZMod 20543) ^ 10271 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (10271 : ZMod 20543)
      decide
    · change IsUnit ((5 : ZMod 20543) ^ 2 - 1)
      rw [← natCast_fastPowMod_eq_pow]
      apply IsUnit.of_mul_eq_one (856 : ZMod 20543)
      decide
  · norm_num
set_option maxHeartbeats 20000000 in
def dusartPrimeRows_19937_20958_part08 : List DusartPrimeRow :=
  [
    dusartPrimeRow_of_explicit_20952 (p := 20443) (q := 20477) (by exact lowPrime_20477) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20477) (q := 20479) (by exact lowPrime_20479) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20479) (q := 20483) (by exact lowPrime_20483) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20483) (q := 20507) (by exact lowPrime_20507) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20507) (q := 20509) (by exact lowPrime_20509) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20509) (q := 20521) (by exact lowPrime_20521) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20521) (q := 20533) (by exact lowPrime_20533) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    dusartPrimeRow_of_explicit_20952 (p := 20533) (q := 20543) (by exact lowPrime_20543) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
  ]

set_option maxHeartbeats 20000000 in
theorem dusartPrimeRows_19937_20958_part08_chain :
    DusartPrimeRowsChain 20443 20543 dusartPrimeRows_19937_20958_part08 := by
  apply DusartPrimeRowsChain.cons
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · norm_num [dusartPrimeRow_of_explicit_20952]
  · apply DusartPrimeRowsChain.cons
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · norm_num [dusartPrimeRow_of_explicit_20952]
    · apply DusartPrimeRowsChain.cons
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · norm_num [dusartPrimeRow_of_explicit_20952]
      · apply DusartPrimeRowsChain.cons
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · norm_num [dusartPrimeRow_of_explicit_20952]
        · apply DusartPrimeRowsChain.cons
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · norm_num [dusartPrimeRow_of_explicit_20952]
          · apply DusartPrimeRowsChain.cons
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · norm_num [dusartPrimeRow_of_explicit_20952]
            · apply DusartPrimeRowsChain.cons
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · norm_num [dusartPrimeRow_of_explicit_20952]
              · apply DusartPrimeRowsChain.cons
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · norm_num [dusartPrimeRow_of_explicit_20952]
                · apply DusartPrimeRowsChain.empty
                  norm_num
